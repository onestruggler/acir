#!/usr/bin/env python3
"""Decoded Table 1 relations on four wires, and how they split into
runs of the subgroups P_w.

    python3 -B dec4.py [family ...]

P_w is the image of the three-wire CCX+H group under H_i -> HH(i, w):
the circuits that use wire w only through HH gates.  Its generators are
the gates avoiding w and every HH.  A run is a maximal segment whose
gates all generate one P_w."""
import sys
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]          # Examples/Groups
sys.path.insert(0, str(ROOT / 'CCX+HH' / 'GeneralN'))
sys.path.insert(0, str(ROOT / 'CCX+HH' / 'scripts'))
sys.path.insert(0, str(ROOT / 'CCX+H' / 'Rules3'))
import normalize as NZ
from table import T1, instances

W = 4
REP = {(0, 0): (), (1, 0): (('M', (0,)),), (1, 1): (('X', (0, 1)),),
       (0, 1): (('M', (0,)), ('X', (0, 1)))}


def letter(t, v):
    if t[0] == 'M':
        return ('M', (v[t[1]],))
    if t[0] == 'X':
        return ('X', (v[t[1]], v[t[2]]))
    return ('K', tuple(v[x] for x in t[1:]))


def relator(con, v, c):
    lhs = [letter(t, v) for t in con[3]]
    rhs = [letter(t, v) for t in con[4]]
    r = REP[c]
    return tuple(r) + tuple(lhs) + tuple(reversed(rhs)) + tuple(reversed(r))


def wires_of(g):
    return set(g[1])


def adm(g):
    if g[0] == 'HH':
        return {0, 1, 2, 3}
    return {0, 1, 2, 3} - wires_of(g)


def runs(word):
    out = []
    cur, s = [], {0, 1, 2, 3}
    for g in word:
        a = adm(g)
        if cur and not (s & a):
            out.append((s, len(cur)))
            cur, s = [], {0, 1, 2, 3}
        cur.append(g)
        s &= a
    if cur:
        out.append((s, len(cur)))
    return out


def lde_profile(word):
    m = NZ.dyadic.identity(W)
    prof = []
    for g in word:
        m = NZ.physical_matrix(W, (g,)) if False else m
    return prof


def stats(word):
    hh = sum(1 for g in word if g[0] == 'HH')
    rs = runs(word)
    return len(word), hh, len(rs)


if __name__ == '__main__':
    fams = sys.argv[1:] or [c[0] for c in T1]
    for con in T1:
        if con[0] not in fams:
            continue
        ins = [v for v in instances(con)]
        # instances() is on eight levels; take the first few
        for v in ins[:2]:
            for c in REP:
                src = relator(con, v, c)
                word = NZ.decode_dyadic(W, src)
                word = NZ.cancel_involutions(word)
                m = NZ.physical_matrix(W, word)
                ok = m == NZ.dyadic.identity(W)
                n, hh, nr = stats(word)
                print(f'{con[0]} {v} c={c}: identity={ok} gates={n} HH={hh} runs={nr}', flush=True)
