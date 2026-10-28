"""Subcase 3.2.5 on Fin 4: [K] ~ V [K] S (even) and [K] S' [K] ~ V [K] S (odd)."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import itertools, json, sys, time
from rules import N, X, K
from passtools import *
from sides2 import apply_all
from sptools import sp_derive
from alg import ident as aident, word_apply
from sp import sp_word, as_sp
m = 4
KK = K(0, 1, 2, 3)
ALL = [tuple(sg[j] * (perm[j] + 1) for j in range(m))
       for perm in itertools.permutations(range(m)) for sg in itertools.product([1, -1], repeat=m)]
def mat(w): return word_apply(list(w), aident(m))
def spw(M):
    r = as_sp(M)
    return None if r is None else sp_word(M)

def even(S):
    lhs = (KK,)
    V = sp_word(mat([KK] + list(reversed(S)) + [KK]))
    st, w = refactor(lhs, 0, 0, 1, V, (0, 1, 2, 3), tuple(S), m)
    return V, st

def odd(S2, S):
    lhs = (KK,) + tuple(S2) + (KK,)
    Vm = mat([KK] + list(S2) + [KK] + list(reversed(S)) + [KK])
    V = sp_word(Vm)
    best = None
    for u in ALL:
        uw = word_of_sp(u)
        vw = word_of_sp(comp(sp_of_word((N(0),), m), comp(inv(u), sp_of_word(S2, m))))
        u2 = spw(mat([KK] + list(uw) + [KK]))
        v2 = spw(mat([KK] + list(vw) + [KK]))
        if u2 is None or v2 is None:
            continue
        c = len(uw) + len(vw)
        if best is None or c < best[0]:
            best = (c, uw, vw, u2, v2)
    c, uw, vw, u2, v2 = best
    steps = sp_derive(tuple(S2), uw + (N(0),) + vw, m, off=1)
    w = apply_all(lhs, steps)
    st, w = refactor(w, 0, 0, 1 + len(uw), u2, (0, 1, 2, 3), (), m); steps += st
    k2 = len(u2) + 2 + len(vw)
    st, w = refactor(w, len(u2) + 2, k2, k2 + 1, (), (0, 1, 2, 3), v2, m); steps += st
    p = len(u2)
    st = [('knk0', [0, 1, 2, 3], True, p)]
    w = apply_all(w, st); steps += st
    # w = u2 X12 N0 K N0 v2
    kp = len(u2) + 2
    st, w = refactor(w, 0, kp, len(w), V, (0, 1, 2, 3), tuple(S), m); steps += st
    assert w == V + (KK,) + tuple(S)
    return V, steps

if __name__ == '__main__':
    res = {}
    bits = list(itertools.product([0, 1], repeat=4))
    sg = lambda t: tuple(N(i) for i in range(4) if t[i])
    for t in bits:
        if sum(t) % 2 == 0:
            V, st = even(sg(t))
            res['e' + ''.join(map(str, t))] = (V, st)
            print('e', t, len(V), len(st))
    for t in bits:
        if sum(t) % 2 == 0: continue
        for t2 in bits:
            if sum(t2) % 2 == 0: continue
            V, st = odd(sg(t2), sg(t))
            res['o' + ''.join(map(str, t)) + ''.join(map(str, t2))] = (V, st)
            print('o', t, t2, len(V), len(st)); sys.stdout.flush()
    json.dump(res, open(os.path.join(HERE, 'd325.json'), 'w'))
    print(len(res), sum(len(v[1]) for v in res.values()))
