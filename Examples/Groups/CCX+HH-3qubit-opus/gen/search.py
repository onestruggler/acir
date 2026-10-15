"""Derivation search over words, by bidirectional breadth-first search.

A lemma is (name, lhs, rhs) with a derivation; it may be used in either
orientation, but only with a nonempty left side as the pattern.  A path
is a list of (position, name, orientation) steps, orientation +1 for
lhs -> rhs and -1 for rhs -> lhs.
"""
from collections import deque
from model import same, W


class Lib:
    def __init__(self):
        self.lemmas = {}          # name -> (lhs, rhs)
        self.order = []
        self.by_first = {}        # letter -> list of (name, orient, pattern, replacement)

    def add(self, name, lhs, rhs, check=True):
        lhs, rhs = W(lhs), W(rhs)
        if check:
            assert same(lhs, rhs), ('unsound', name, lhs, rhs)
        assert name not in self.lemmas, name
        self.lemmas[name] = (lhs, rhs)
        self.order.append(name)
        for o, p, q in ((1, lhs, rhs), (-1, rhs, lhs)):
            if p:
                self.by_first.setdefault(p[0], []).append((name, o, p, q))

    def moves(self, w, maxlen, only=None):
        n = len(w)
        for i in range(n):
            for (name, o, p, q) in self.by_first.get(w[i], ()):
                if only is not None and name not in only:
                    continue
                m = len(p)
                if w[i:i + m] == p:
                    nw = w[:i] + q + w[i + m:]
                    if len(nw) <= maxlen:
                        yield nw, (i, name, o)


def bfs(lib, u, v, maxlen=None, maxnodes=2_000_000, only=None):
    u, v = W(u), W(v)
    if u == v:
        return []
    if maxlen is None:
        maxlen = max(len(u), len(v)) + 4
    # parents: word -> (prev word, step) ; separate for both sides
    pa = {u: None}
    pb = {v: None}
    qa, qb = deque([u]), deque([v])
    nodes = 0
    while qa or qb:
        # expand the smaller nonempty frontier, one whole level
        if qa and (not qb or len(qa) <= len(qb)):
            q, par, other, side = qa, pa, pb, 'a'
        else:
            q, par, other, side = qb, pb, pa, 'b'
        for _ in range(len(q)):
            w = q.popleft()
            for nw, st in lib.moves(w, maxlen, only):
                if nw in par:
                    continue
                par[nw] = (w, st)
                nodes += 1
                if nw in other:
                    return assemble(pa, pb, nw, lib)
                q.append(nw)
            if nodes > maxnodes:
                return None
    return None


def assemble(pa, pb, mid, lib):
    # path from u to mid
    left = []
    w = mid
    while pa[w] is not None:
        pw, st = pa[w]
        left.append((pw, st))
        w = pw
    left.reverse()
    steps = [st for (_, st) in left]
    # path from mid to v: pb records v-side moves (applied from v outwards);
    # going mid -> v reverses each of them.
    w = mid
    while pb[w] is not None:
        pw, (i, name, o) = pb[w]
        # pw --(i,name,o)--> w ; so w --(i,name,-o)--> pw
        steps.append((i, name, -o))
        w = pw
    return steps


def replay(lib, u, steps):
    w = W(u)
    for (i, name, o) in steps:
        l, r = lib.lemmas[name]
        p, q = (l, r) if o == 1 else (r, l)
        assert w[i:i + len(p)] == p, (w, i, name, o)
        w = w[:i] + q + w[i + len(p):]
    return w
