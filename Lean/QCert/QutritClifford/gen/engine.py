"""The derivation engine, as checked in Lean (`Engine.lean`).

Width k in {2, 3}.  Words are letter lists in time order over the letters
of qc.py (('H', j), ('S', j), ('CZ', j)); scalars are dropped (equations
hold up to a power of -omega).

`canon` is the lexicographically least word in the class of a word under
commuting adjacent letters on disjoint wires (`lexmin`), with the letter
order `rank`.  A derivation of `lhs = rhs` is a list of steps from `lhs`:

* ('rule', i, d, u, v): canon cur = canon (u ++ L ++ v), next = u ++ R ++ v,
  where (L, R) is entry i of the table, swapped when d is True;
* ('free', w, u, s, t, v): canon cur = canon (u ++ s ++ v), s and t lie in
  window w (a set of k - 1 adjacent wires) and have the same projective
  action there; next = u ++ t ++ v;

and finally canon cur = canon rhs.  The table starts with the base rules
and grows by every lemma checked so far.
"""
import cliff
import qc


def rank(l):
    kind = {'H': 0, 'S': 1, 'CZ': 2}[l[0]]
    return (l[1], kind)


def lexmin(w):
    """Repeatedly take the least letter that commutes with every letter
    before it."""
    w = list(w)
    out = []
    while w:
        best = 0
        for i in range(1, len(w)):
            if rank(w[i]) < rank(w[best]) and all(cliff.commute(w[i], w[j]) for j in range(i)):
                best = i
        out.append(w.pop(best))
    return out


def windows(k):
    return [tuple(range(j, j + k - 1)) for j in range(2)]


def in_window(seg, win):
    return all(cliff.wires(l) <= set(win) for l in seg)


def same_window_action(s, t, win):
    lo = win[0]
    m = len(win)
    return cliff.key(qc.up(s, -lo), m) == cliff.key(qc.up(t, -lo), m)


class Engine:
    def __init__(self, k, base):
        """base: list of (name, lhs, rhs)."""
        self.k = k
        self.table = []
        self.names = {}
        for name, l, r in base:
            self._add(name, l, r)
        self.nbase = len(self.table)
        self.lemmas = []      # (name, lhs, rhs, steps)

    def _add(self, name, l, r):
        assert cliff.key(l, self.k) == cliff.key(r, self.k), name
        self.names[name] = len(self.table)
        self.table.append((list(l), list(r)))

    def run(self, lhs, steps):
        cur = list(lhs)
        for st in steps:
            if st[0] == 'rule':
                _, i, d, u, v = st
                L, R = self.table[i]
                if d:
                    L, R = R, L
                assert lexmin(cur) == lexmin(u + L + v), ('rule', i)
                cur = u + R + v
            else:
                _, w, u, s, t, v = st
                win = windows(self.k)[w]
                assert lexmin(cur) == lexmin(u + s + v), 'free canon'
                assert in_window(s, win) and in_window(t, win), 'free window'
                assert same_window_action(s, t, win), 'free action'
                cur = u + t + v
        return cur

    def lemma(self, name, lhs, rhs, steps):
        cur = self.run(lhs, steps)
        assert lexmin(cur) == lexmin(rhs), ('end', name)
        self.lemmas.append((name, list(lhs), list(rhs), steps))
        self._add(name, lhs, rhs)
        return self.names[name]

    # ---- building steps from a chain of words -------------------------

    def factors(self, a, x):
        """Splittings u, v with u ++ x ++ v in the class of a: x taken from
        increasing positions of a, every skipped letter commuting with the
        letters of x taken before it (and so moved in front)."""
        out = []
        if not x:
            return [(list(a[:p]), list(a[p:])) for p in range(len(a) + 1)]
        for s in range(len(a)):
            if a[s] != x[0]:
                continue
            taken = [s]
            pre = list(a[:s])
            ok = True
            j = 1
            p = s + 1
            while j < len(x):
                while p < len(a) and a[p] != x[j]:
                    if all(cliff.commute(a[p], a[t]) for t in taken):
                        pre.append(a[p])
                        p += 1
                    else:
                        ok = False
                        break
                if not ok or p >= len(a):
                    ok = False
                    break
                taken.append(p)
                p += 1
                j += 1
            if ok:
                u, v = pre, list(a[p:])
                if lexmin(u + x + v) == lexmin(a):
                    out.append((u, v))
        return out

    def step(self, a, b):
        """One step taking a to (a word canon-equal to) b."""
        la, lb = lexmin(a), lexmin(b)
        # rule steps, matched in the class of a
        for i, (L, R) in enumerate(self.table):
            for d, (x, y) in ((False, (L, R)), (True, (R, L))):
                for u, v in self.factors(a, x):
                    if lexmin(u + y + v) == lb:
                        return ('rule', i, d, u, v), u + y + v
        # free steps: common prefix and suffix
        for w, win in enumerate(windows(self.k)):
            p = 0
            while p < min(len(a), len(b)) and a[p] == b[p]:
                p += 1
            s = 0
            while s < min(len(a), len(b)) - p and a[len(a) - 1 - s] == b[len(b) - 1 - s]:
                s += 1
            sa, sb = a[p:len(a) - s], b[p:len(b) - s]
            if in_window(sa, win) and in_window(sb, win) and same_window_action(sa, sb, win):
                u, v = a[:p], a[len(a) - s:]
                return ('free', w, u, sa, sb, v), u + sb + v
        return None, None

    def chain(self, name, words, rhs=None):
        """Lemma from a chain of words (consecutive words one step apart;
        a word may differ from the previous one only by canon)."""
        steps = []
        cur = list(words[0])
        for b in words[1:]:
            if lexmin(cur) == lexmin(b):
                cur = list(b)
                continue
            st, nxt = self.step(cur, list(b))
            if st is None:
                raise ValueError('%s: no step\n  %s\n  %s' % (name, cur, b))
            steps.append(st)
            cur = list(b)
        rhs = words[-1] if rhs is None else rhs
        return self.lemma(name, words[0], rhs, steps)
