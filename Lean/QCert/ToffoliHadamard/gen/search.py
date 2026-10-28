"""Bidirectional breadth-first search for derivations.

A rule is (lhs, rhs) over letters (small ints), stored as bytes.  A step
is (pos, rule index, direction); direction True applies lhs -> rhs.
"""
from collections import deque

class RuleSet:
    def __init__(self):
        self.rules = []      # (lhs bytes, rhs bytes, name)
        self.index = {}      # lhs -> list of (rhs, rule id, direction)
        self.lens = set()
        self.ins = []
        self.use_ins = True        # (word inserted, rule id, direction) for rules with an empty side

    def add(self, l, r, name, both=True):
        l = bytes(l); r = bytes(r)
        k = len(self.rules)
        self.rules.append((l, r, name))
        if len(l) > 0:
            self.index.setdefault(l, []).append((r, k, True))
            self.lens.add(len(l))
        elif both:
            self.ins.append((r, k, True))
        if both and len(r) > 0:
            self.index.setdefault(r, []).append((l, k, False))
            self.lens.add(len(r))
        elif both and len(r) == 0 and len(l) > 0:
            self.ins.append((l, k, False))
        return k

    def neighbours(self, w, maxlen):
        n = len(w)
        lens = sorted(self.lens)
        for i in range(n):
            for ln in lens:
                if i + ln > n:
                    break
                seg = w[i:i + ln]
                lst = self.index.get(seg)
                if lst is None:
                    continue
                for (r, k, d) in lst:
                    nw = w[:i] + r + w[i + ln:]
                    if len(nw) <= maxlen:
                        yield nw, (i, k, d)
        if self.use_ins:
            for (r, k, d) in self.ins:
                if n + len(r) <= maxlen:
                    for i in range(n + 1):
                        yield w[:i] + r + w[i:], (i, k, d)


def bidir(rs, a, b, maxlen=None, limit=2_000_000, verbose=False):
    a = bytes(a); b = bytes(b)
    if a == b:
        return []
    if maxlen is None:
        maxlen = max(len(a), len(b)) + 2
    pa = {a: None}; pb = {b: None}
    fa = [a]; fb = [b]
    seen = 0
    while fa or fb:
        if fa and (not fb or len(fa) <= len(fb)):
            nf = []
            for w in fa:
                for nw, st in rs.neighbours(w, maxlen):
                    if nw in pa:
                        continue
                    pa[nw] = (w, st)
                    if nw in pb:
                        return _join(rs, pa, pb, nw)
                    nf.append(nw)
            fa = nf
        else:
            nf = []
            for w in fb:
                for nw, st in rs.neighbours(w, maxlen):
                    if nw in pb:
                        continue
                    pb[nw] = (w, st)
                    if nw in pa:
                        return _join(rs, pa, pb, nw)
                    nf.append(nw)
            fb = nf
        seen = len(pa) + len(pb)
        if verbose:
            print("  frontier", len(fa), len(fb), seen)
        if seen > limit:
            return None
    return None


def _path(par, w):
    steps = []
    while par[w] is not None:
        pw, st = par[w]
        steps.append((pw, st, w))
        w = pw
    steps.reverse()
    return steps


def _join(rs, pa, pb, m):
    # forward steps from a to m, then reversed steps from m to b
    fwd = _path(pa, m)
    bwd = _path(pb, m)
    out = [(st, nw) for (pw, st, nw) in fwd]
    for (pw, st, nw) in reversed(bwd):
        # step st took pw to nw (from b's side); undo it: nw -> pw
        i, k, d = st
        out.append(((i, k, not d), pw))
    return out


def replay(rs, w, steps):
    w = bytes(w)
    for (i, k, d), _ in steps:
        l, r, _n = rs.rules[k]
        src, dst = (l, r) if d else (r, l)
        assert w[i:i + len(src)] == src, (w, i, src)
        w = w[:i] + dst + w[i + len(src):]
    return w
