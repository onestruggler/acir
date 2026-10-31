"""Knuth–Bendix completion with derivations, over a proof table (`table.Table`).

A rule `lhs -> rhs` is an equation of the table used in one direction: applying the step
(pos, eid, d) at the position of `lhs` produces `rhs`.  Every rule created by completion is
an equation derived (in the table) from the rules before it.  The ordering is given by a key
function on words (default: weighted shortlex).
"""
import time
from collections import deque
from table import invert


class KB:
    def __init__(self, T, letters, weight=None, rank=None, keyfn=None, verbose=False, maxlen=60):
        self.T = T
        self.letters = list(letters)
        self.rank = rank or {a: i for i, a in enumerate(self.letters)}
        self.weight = weight or {a: 1 for a in self.letters}
        self.keyfn = keyfn
        self.rules = {}        # lhs -> (rhs, eid, d)
        self.lens = []
        self.maxlhs = 0
        self.verbose = verbose
        self.maxlen = maxlen
        self.queue = deque()   # lhs of rules whose critical pairs are not yet computed
        self.byfirst = {}      # first letter -> set of lhs

    def key(self, w):
        if self.keyfn:
            return self.keyfn(w)
        return (sum(self.weight[a] for a in w), len(w), tuple(self.rank[a] for a in w))

    def reduce(self, w, steps=None):
        """Reduce w to its normal form, appending steps (pos, eid, d) to `steps`."""
        w = tuple(w)
        if steps is None:
            steps = []
        rules = self.rules
        lens = self.lens
        i = 0
        n = len(w)
        while i < n:
            hit = False
            for L in lens:
                if i + L > n:
                    break
                r = rules.get(w[i:i + L])
                if r is not None:
                    rhs, eid, d = r
                    steps.append((i, eid, d))
                    w = w[:i] + rhs + w[i + L:]
                    n = len(w)
                    i = max(0, i - self.maxlhs + 1)
                    hit = True
                    break
            if not hit:
                i += 1
        return w, steps

    def is_reducible(self, w):
        rules = self.rules
        for i in range(len(w)):
            for L in self.lens:
                if i + L > len(w):
                    break
                if w[i:i + L] in rules:
                    return True
        return False

    def _set_lens(self):
        self.lens = sorted({len(l) for l in self.rules})
        self.maxlhs = max(self.lens) if self.lens else 0

    def add_rule(self, lhs, rhs, eid, d):
        removed = []
        for l2 in list(self.rules):
            if l2 != lhs and _contains(l2, lhs):
                removed.append((l2,) + self.rules.pop(l2))
                self.byfirst[l2[0]].discard(l2)
        self.rules[lhs] = (rhs, eid, d)
        self.byfirst.setdefault(lhs[0], set()).add(lhs)
        self._set_lens()
        self.queue.append(lhs)
        for l2, r2, e2, d2 in removed:
            el, er, _ = self.T.eqs[e2]
            self._add_pair(el, er, e2)

    def add_equation(self, eid):
        l, r, _ = self.T.eqs[eid]
        return self._add_pair(l, r, eid)

    def _add_pair(self, l, r, eid):
        """T.eqs[eid] = (l, r): reduce both sides, orient, add."""
        nl, sl = self.reduce(l)
        nr, sr = self.reduce(r)
        if nl == nr:
            return None
        if (nl, nr) == (l, r):
            e2 = eid
        else:
            e2 = self.T.derived(nl, nr, invert(sl) + [(0, eid, True)] + sr)
        if self.key(nl) > self.key(nr):
            self.add_rule(nl, nr, e2, True)
        else:
            self.add_rule(nr, nl, e2, False)
        return e2

    def _overlaps(self, l1, r1, e1, d1, l2, r2, e2, d2):
        """Critical pairs of l1 (left) and l2 (right): a proper suffix of l1 = prefix of l2."""
        for k in range(1, min(len(l1), len(l2))):
            if l1[-k:] == l2[:k]:
                w_len = len(l1) + len(l2) - k
                if w_len > self.maxlen:
                    continue
                a = r1 + l2[k:]
                b = l1[:len(l1) - k] + r2
                na, sa = self.reduce(a)
                nb, sb = self.reduce(b)
                if na == nb:
                    continue
                steps = invert(sa) + [(0, e1, not d1)] + [(len(l1) - k, e2, d2)] + sb
                e = self.T.derived(na, nb, steps)
                self._add_pair(na, nb, e)

    def complete(self, maxrules=200000, maxtime=600):
        t0 = time.time()
        cnt = 0
        while self.queue:
            l1 = self.queue.popleft()
            if l1 not in self.rules:
                continue
            for l2 in list(self.rules):
                if l1 not in self.rules:
                    break
                if l2 not in self.rules:
                    continue
                r1, e1, d1 = self.rules[l1]
                r2, e2, d2 = self.rules[l2]
                self._overlaps(l1, r1, e1, d1, l2, r2, e2, d2)
                if l2 != l1 and l1 in self.rules and l2 in self.rules:
                    r1, e1, d1 = self.rules[l1]
                    r2, e2, d2 = self.rules[l2]
                    self._overlaps(l2, r2, e2, d2, l1, r1, e1, d1)
            cnt += 1
            if self.verbose and cnt % 200 == 0:
                print('  kb rules', len(self.rules), 'queue', len(self.queue),
                      'time %.1f' % (time.time() - t0), flush=True)
            if len(self.rules) > maxrules or time.time() - t0 > maxtime:
                return False
        return True


def _contains(w, s):
    n = len(s)
    for i in range(len(w) - n + 1):
        if w[i:i + n] == s:
            return True
    return False


def count_nf(kb, limit=10**7):
    """Number of irreducible words (BFS by length; normal forms are suffix- and prefix-closed)."""
    letters = kb.letters
    level = [()]
    total = 1
    while level:
        nxt = []
        for w in level:
            for a in letters:
                v = w + (a,)
                ok = True
                for L in kb.lens:
                    if L > len(v):
                        break
                    if v[-L:] in kb.rules:
                        ok = False
                        break
                if ok:
                    nxt.append(v)
        total += len(nxt)
        if total > limit:
            return None
        level = nxt
    return total
