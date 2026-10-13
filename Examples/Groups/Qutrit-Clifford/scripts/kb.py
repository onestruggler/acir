"""Knuth-Bendix completion with derivations.

Words are strings over a finite alphabet; ORDER gives the letters' rank
(shortlex).  Every equation ever created is kept, with a derivation: a
list of steps (pos, eq id, dir) rewriting the current word at pos with
that equation left to right (dir +1) or right to left (dir -1)."""
import sys, time

class KB:
    def __init__(self, order):
        self.order = order
        self.eqs = {}          # id -> dict(l, r, name, steps)
        self.active = {}       # id -> dir (the rule src -> dst)
        self.index = {}        # first letter of src -> set of ids
        self.next = 0
        self.pending = []

    def key(self, w):
        return (len(w), [self.order[c] for c in w])

    def new_eq(self, l, r, steps=None, name=None):
        i = self.next; self.next += 1
        self.eqs[i] = dict(l=l, r=r, name=name, steps=steps)
        return i

    def axiom(self, l, r, name):
        i = self.new_eq(l, r, name=name)
        self.pending.append((l, r, [(0, i, 1)]))
        return i

    def src(self, i):
        e = self.eqs[i]; return e['l'] if self.active[i] > 0 else e['r']
    def dst(self, i):
        e = self.eqs[i]; return e['r'] if self.active[i] > 0 else e['l']

    def apply(self, w, pos, i, d):
        if i == 'P':
            src, dst = d
            assert w[pos:pos + len(src)] == src, (w, pos, src)
            return w[:pos] + dst + w[pos + len(src):]
        e = self.eqs[i]
        a, b = (e['l'], e['r']) if d > 0 else (e['r'], e['l'])
        assert w[pos:pos + len(a)] == a, (w, pos, i, d)
        return w[:pos] + b + w[pos + len(a):]

    def find(self, w):
        for p in range(len(w)):
            for i in self.index.get(w[p], ()):
                s = self.src(i)
                if w.startswith(s, p):
                    return p, i
        return None

    def normalise(self, w):
        steps = []
        while True:
            f = self.find(w)
            if f is None: return w, steps
            p, i = f
            d = self.active[i]
            w = self.apply(w, p, i, d)
            steps.append((p, i, d))

    @staticmethod
    def reverse(steps):
        return [(p, i, (d[1], d[0]) if i == 'P' else -d) for (p, i, d) in reversed(steps)]

    def check_path(self, a, steps, b):
        w = a
        for p, i, d in steps:
            w = self.apply(w, p, i, d)
        assert w == b, (a, b, w)

    def activate(self, i, d):
        self.active[i] = d
        self.index.setdefault(self.src(i)[0], set()).add(i)

    def deactivate(self, i):
        self.index[self.src(i)[0]].discard(i)
        del self.active[i]

    def add_pair(self, a, b, path):
        na, sa = self.normalise(a)
        nb, sb = self.normalise(b)
        if na == nb: return None
        full = self.reverse(sa) + path + sb
        if self.key(na) > self.key(nb):
            l, r, st = na, nb, full
        else:
            l, r, st = nb, na, self.reverse(full)
        i = self.new_eq(l, r, steps=st)
        # interreduce: rules whose source contains l
        for j in list(self.active):
            s = self.src(j)
            if l in s:
                self.pending.append((s, self.dst(j), [(0, j, self.active[j])]))
                self.deactivate(j)
        self.activate(i, 1)
        return i

    def overlaps(self, i, j):
        l1, l2 = self.src(i), self.src(j)
        d1, d2 = self.active[i], self.active[j]
        out = []
        for k in range(1, min(len(l1), len(l2))):
            if l1[-k:] == l2[:k]:
                w = l1 + l2[k:]
                a = self.apply(w, 0, i, d1)
                b = self.apply(w, len(l1) - k, j, d2)
                out.append((a, [(0, i, -d1), (len(l1) - k, j, d2)], b))
        if i != j:
            p = l1.find(l2)
            while p >= 0:
                a = self.apply(l1, 0, i, d1)
                b = self.apply(l1, p, j, d2)
                out.append((a, [(0, i, -d1), (p, j, d2)], b))
                p = l1.find(l2, p + 1)
        return out

    def flush(self):
        while self.pending:
            a, b, path = self.pending.pop(0)
            self.add_pair(a, b, path)

    def complete(self, limit=None, maxlen=None, timeout=None, verbose=False):
        t0 = time.time()
        done = set()
        self.flush()
        while True:
            new = False
            for i in sorted(self.active):
                for j in sorted(self.active):
                    if i not in self.active or j not in self.active: continue
                    if (i, j) in done: continue
                    done.add((i, j))
                    if maxlen and len(self.src(i)) + len(self.src(j)) > maxlen: continue
                    for a, path, b in self.overlaps(i, j):
                        self.pending.append((a, b, path)); new = True
                    self.flush()
                    if limit and len(self.active) > limit:
                        return False
                    if timeout and time.time() - t0 > timeout:
                        return False
            if verbose:
                print('pass: active %d eqs %d' % (len(self.active), len(self.eqs)), file=sys.stderr)
            if not new: return True

    def needed(self, steps_lists):
        need = set()
        stack = [i for st in steps_lists for (_, i, _) in st if i != 'P']
        while stack:
            i = stack.pop()
            if i in need: continue
            need.add(i)
            if self.eqs[i]['steps']:
                stack += [j for (_, j, _) in self.eqs[i]['steps'] if j != 'P']
        return need
