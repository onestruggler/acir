#!/usr/bin/env python3
"""The canonical decoded relations on four wires: what they are made of.

The auxiliary presentation (Subgroup/) has Schreier generators, edges
(c, g) read as rep(c) · g · rep(c·g)⁻¹, at the four states with
representatives ε, M0, X01, M0 X01.  Each Table 1 relation, rewritten
at each state, is a word in edges.  Up to the classical permutations of
the levels fixing 0 and 1 there are 109 patterns (`patterns4.py`), so
436 canonical rewritten relations.

An edge is a signed permutation (from M and X) or a signed permutation
times a K on four levels.  This script computes, for each canonical
relation: its edges, how many are K-edges, the quadruples of those, and
whether the relation already holds among the signed-permutation edges
alone (no K), i.e. lies in the signed classical group.

    python3 -B canon4.py
"""
import itertools
import sys
from collections import Counter
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / 'CCX+H' / 'Rules3'))
import table as TB

D = 16
STATES = ((0, 0), (1, 0), (1, 1), (0, 1))
REPS = {(0, 0): (), (1, 0): (('M', (0,)),), (1, 1): (('X', (0, 1)),),
        (0, 1): (('M', (0,)), ('X', (0, 1)))}
CHARGE = {'M': (1, 0), 'X': (1, 1), 'K': (0, 1)}


def step(c, g):
    x, y = CHARGE[g[0]]
    return c[0] ^ x, c[1] ^ y


# ---------------------------------------------------------------------
# exact matrices, as dicts of rows: m[r][c] = Fraction
def ident():
    return [[Fr(int(r == c)) for c in range(D)] for r in range(D)]


def mul(a, b):
    out = [[Fr(0)] * D for _ in range(D)]
    for i in range(D):
        ai = a[i]
        for k in range(D):
            if ai[k]:
                bk = b[k]
                for j in range(D):
                    if bk[j]:
                        out[i][j] += ai[k] * bk[j]
    return out


def letter(g):
    m = ident()
    k, ix = g
    if k == 'M':
        m[ix[0]][ix[0]] = Fr(-1)
    elif k == 'X':
        a, b = ix
        m[a][a] = m[b][b] = Fr(0)
        m[a][b] = m[b][a] = Fr(1)
    else:
        for r in ix:
            for c in ix:
                m[r][c] = Fr(0)
        for i, r in enumerate(ix):
            for j, c in enumerate(ix):
                m[r][c] = Fr((-1) ** bin(i & j).count('1'), 2)
    return m


def word(ws):
    m = ident()
    for g in ws:
        m = mul(m, letter(g))
    return m


def is_monomial(m):
    return all(sum(1 for x in row if x) == 1 and all(x in (0, 1, -1) for x in row) for row in m)


def support(m):
    """Levels where m is not monomial."""
    return tuple(i for i, row in enumerate(m) if sum(1 for x in row if x) != 1)


# ---------------------------------------------------------------------
def edge(c, g):
    c2 = step(c, g)
    ws = REPS[c] + (g,) + tuple(reversed(REPS[c2]))
    return c2, ws


def relator(con, v):
    name, vs, args, lhs, rhs = con[:5]

    def lt(t):
        if t[0] == 'M':
            return ('M', (v[t[1]],))
        if t[0] == 'X':
            return ('X', (v[t[1]], v[t[2]]))
        return ('K', tuple(v[x] for x in t[1:]))
    return [lt(t) for t in lhs] + [lt(t) for t in reversed(rhs)]


def instance(con, pattern):
    """A concrete instance of a pattern (0, 1 kept, other labels to
    distinct levels ≥ 2 satisfying the constraints)."""
    name, vs, args = con[0], con[1].split(), con[2]
    labels = sorted({x for x in pattern if x >= 2})

    def full(m):
        return {vs[j]: (pattern[j] if pattern[j] < 2 else m[pattern[j]]) for j in range(len(vs))}

    def ok_partial(m):
        # check the constraints whose variables are all assigned
        v = {vs[j]: (pattern[j] if pattern[j] < 2 else m.get(pattern[j])) for j in range(len(vs))}
        return all(TB.holds(a, v) for a in args
                   if all(v[x] is not None for x in a[1:] if isinstance(x, str) and x in v))

    def rec(i, m, used):
        if i == len(labels):
            v = full(m)
            return v if all(TB.holds(a, v) for a in args) else None
        for val in range(2, D):
            if val in used:
                continue
            m[labels[i]] = val
            if ok_partial(m):
                r = rec(i + 1, m, used | {val})
                if r is not None:
                    return r
            del m[labels[i]]
        return None
    return rec(0, {}, frozenset())


def patterns(con):
    vs = con[1].split()
    out = []

    def rec(i, assign, nxt):
        if i == len(vs):
            if instance(con, assign) is not None:
                out.append(tuple(assign))
            return
        for val in [0, 1] + list(range(2, nxt + 1)):
            rec(i + 1, assign + [val], max(nxt, val + 1) if val >= 2 else nxt)
    rec(0, [], 2)
    return out


def main():
    tot = 0
    kinds = Counter()
    kcount = Counter()
    for con in TB.T1:
        for pat in patterns(con):
            v = instance(con, pat)
            r = relator(con, v)
            for c in STATES:
                state, edges = c, []
                for g in r:
                    state2, ws = edge(state, g)
                    edges.append((state, g, ws))
                    state = state2
                assert state == c
                nk = sum(1 for _, g, _ in edges if g[0] == 'K')
                kcount[nk] += 1
                tot += 1
                kinds[(con[0], nk)] += 1
    print('canonical rewritten relations:', tot)
    print('by number of K-edges:', dict(sorted(kcount.items())))
    for (nm, nk), c in sorted(kinds.items()):
        print(f'  {nm}: {c} with {nk} K-edges')


if __name__ == '__main__':
    main()
