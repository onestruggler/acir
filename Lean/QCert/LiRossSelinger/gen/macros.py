"""Derived relation families (macros): each on k sorted indices, given on
0..k-1; instances on Fin m are the renamings along sorted k-subsets."""
from itertools import combinations
from rules import N, X, K

def ren(w, ps):
    out = []
    for g in w:
        out.append((g[0],) + tuple(ps[i] for i in g[1:]))
    return tuple(out)

k4 = K(0, 1, 2, 3)
# name -> (k, lhs, rhs) on 0..k-1
BASE = {
    'ksym2': (4, (X(1, 2), k4), (k4, X(1, 2))),
    'ksym4': (4, (X(0, 2), k4), (k4, X(2, 3), N(2), N(3))),
    'ksym5': (4, (X(0, 3), k4), (k4, X(1, 3), X(2, 3), X(1, 3), N(1), N(2))),
    'ksym6': (4, (X(1, 3), k4), (k4, X(2, 3))),
    'k21': (4, (N(1), N(3), k4), (k4, X(0, 1), X(2, 3))),
    'k11': (4, (N(2), N(3), k4), (k4, X(0, 2), X(1, 3))),
    'k31': (4, (N(1), N(2), k4), (k4, X(0, 3), X(1, 2))),
    'relk4': (4, (N(0), N(1), N(2), N(3), k4), (k4, N(0), N(1), N(2), N(3))),
    'k12': (4, (N(0), N(1), k4), (k4, X(0, 2), X(1, 3), N(0), N(1), N(2), N(3))),
    'k22': (4, (N(0), N(2), k4), (k4, X(0, 1), X(2, 3), N(0), N(1), N(2), N(3))),
    'k32': (4, (N(0), N(3), k4), (k4, X(0, 3), X(1, 2), N(0), N(1), N(2), N(3))),
    'knk0': (4, (k4, N(0), k4), (X(1, 2), N(0), k4, N(0))),
}

def macro_instances(names, m):
    out = []
    for nm in names:
        k, l, r = BASE[nm]
        for ps in combinations(range(m), k):
            out.append((nm, list(ps), ren(l, ps), ren(r, ps)))
    return out
