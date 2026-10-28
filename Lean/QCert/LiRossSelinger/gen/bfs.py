"""Bidirectional BFS for Table 1 derivations between two concrete words.

A step is (fam, ps, dir, pos) as in Lean's Checker: dir True rewrites the
left side of the instance into its right side at position pos."""
from collections import deque
from rules import instances, sides

class Engine:
    def __init__(self, m, fams=None, macros=None, rev=True):
        self.m = m
        self.inst = instances(m, fams)
        # (pattern, replacement, step-template)
        self.by_first = {}
        self.inserts = []
        for fam, ps, l, r in self.inst:
            for (a, b, d) in ((l, r, True), (r, l, False)):
                if len(a) == 0:
                    self.inserts.append((b, (fam, ps, d)))
                else:
                    self.by_first.setdefault(a[0], []).append((a, b, (fam, ps, d)))
        # reversed relations (every generator is an involution): rev_derivable
        if rev:
            for fam, ps, l, r in self.inst:
                if len(l) == 0 or len(r) == 0:
                    continue
                rl, rr = tuple(reversed(l)), tuple(reversed(r))
                if (rl, rr) in ((l, r), (r, l)):
                    continue
                for (a, b, d) in ((rl, rr, True), (rr, rl, False)):
                    self.by_first.setdefault(a[0], []).append((a, b, ('rev_' + fam, ps, d)))
        # macros: list of (name, ps, lhs, rhs) treated like families
        if macros:
            for name, ps, l, r in macros:
                for (a, b, d) in ((l, r, True), (r, l, False)):
                    self.by_first.setdefault(a[0], []).append((a, b, (name, ps, d)))

    def neighbours(self, w, ins_letters=()):
        n = len(w)
        for i in range(n):
            for a, b, st in self.by_first.get(w[i], ()):
                la = len(a)
                if w[i:i + la] == a:
                    yield w[:i] + b + w[i + la:], (st[0], st[1], st[2], i)
        if ins_letters:
            for b, st in self.inserts:
                if b[0] in ins_letters:
                    for i in range(n + 1):
                        yield w[:i] + b + w[i:], (st[0], st[1], st[2], i)

    def search(self, w1, w2, depth=6, maxlen=None, ins_letters=(), limit=2_000_000):
        w1, w2 = tuple(w1), tuple(w2)
        if w1 == w2:
            return []
        if maxlen is None:
            maxlen = max(len(w1), len(w2)) + 2
        par = [{w1: None}, {w2: None}]
        front = [[w1], [w2]]
        for d in range(depth):
            side = 0 if len(front[0]) <= len(front[1]) else 1
            nf = []
            for w in front[side]:
                for v, st in self.neighbours(w, ins_letters):
                    if len(v) > maxlen or v in par[side]:
                        continue
                    par[side][v] = (w, st)
                    if v in par[1 - side]:
                        return self._path(par, v, side)
                    nf.append(v)
                    if len(par[side]) > limit:
                        return None
            front[side] = nf
            if not nf:
                return None
        return None

    def _path(self, par, v, side):
        # chain from w1 to v (forward) and v to w2
        def chain(p, v):
            out = []
            while p[v] is not None:
                u, st = p[v]
                out.append((u, v, st))
                v = u
            return out[::-1]
        a = chain(par[0], v)            # w1 -> v
        b = chain(par[1], v)            # w2 -> v
        steps = [st for (_, _, st) in a]
        for (u, v2, st) in reversed(b):  # v2 -> u by inverting st
            fam, ps, d, pos = st
            steps.append((fam, ps, not d, pos))
        return steps

def apply_steps(w, steps, macros=None):
    md = {}
    if macros:
        for name, ps, l, r in macros:
            md[(name, tuple(ps))] = (l, r)
    w = tuple(w)
    for fam, ps, d, pos in steps:
        if (fam, tuple(ps)) in md:
            l, r = md[(fam, tuple(ps))]
        elif fam.startswith('rev_'):
            l, r = sides(fam[4:], list(ps))
            l, r = tuple(reversed(l)), tuple(reversed(r))
        else:
            l, r = sides(fam, list(ps))
        a, b = (l, r) if d else (r, l)
        assert w[pos:pos + len(a)] == a, (w, fam, ps, d, pos)
        w = w[:pos] + b + w[pos + len(a):]
    return w
