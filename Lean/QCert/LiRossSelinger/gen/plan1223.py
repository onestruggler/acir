"""Subcase 1.2.2.3 on Fin 8 (a..h = 0..7): W^-1 C' W ~ C."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import json
from rules import N, X, K
from passtools import refactor, sp_of_word, word_of_sp, comp, inv
from sides2 import apply_all, move_block
from sptools import sp_derive
from alg import ident as aident, word_apply
m = 8
a, b, c, d, e, f, g, h = range(8)
Kab, Kef = K(a, b, c, d), K(e, f, g, h)
C = (Kef, Kab, X(d, e), Kab, Kef)

def seg(w, i, j, new):
    """sp_derive on the segment w[i:j] -> new."""
    st = sp_derive(tuple(w[i:j]), tuple(new), m, off=i)
    w2 = tuple(w[:i]) + tuple(new) + tuple(w[j:])
    assert apply_all(w, st) == w2
    return st, w2

def swaps(w):
    """K_abcd K_efgh at 3 -> K_efgh K_abcd; K_efgh K_abcd at 6 -> K_abcd K_efgh."""
    st = [('r2f', [a, b, c, d, e, f, g, h], True, 3), ('r2f', [e, f, g, h, a, b, c, d], True, 6)]
    return st, apply_all(w, st)

def E(w, p):
    """X_eh C X_eh at p  ->  C."""
    steps = []
    # refactor (X_eh) K_efgh () -> () K_efgh (y)
    y = word_of_sp(comp(comp(inv(sp_of_word((X(e, h),), m)), ()), ()) if False else ())
    import numpy  # noqa
    # y = K X_eh K semantically
    Ym = word_apply([Kef, X(e, h), Kef], aident(m))
    from sp import sp_word
    y = sp_word(Ym)
    st, w = refactor(w, p, p + 1, p + 2, (), (e, f, g, h), y, m); steps += st
    # w[p] = K_efgh, then y, then K_abcd X_de K_abcd, then K_efgh, X_eh
    i, j, k = p + 1, p + 1 + len(y), p + 1 + len(y) + 3
    st, w2 = move_block(w, i, j, k)
    assert apply_all(w, st) == w2
    w = w2; steps += st
    kp = p + 4 + len(y)
    assert w[kp] == Kef
    st, w = refactor(w, kp - len(y), kp, kp + 2, (), (e, f, g, h), (), m); steps += st
    assert tuple(w[p:p + 5]) == C, w
    return steps, w

def D0():
    W = (N(a), N(e), X(a, e))
    l = tuple(reversed(W)) + (Kab, Kef, X(d, e), Kef, Kab) + W
    steps, w = swaps(l)
    st, w = seg(w, 0, 3, (N(a), N(e), X(a, e))); steps += st
    st, w = seg(w, 8, 11, (X(a, e), N(a), N(e))); steps += st
    st = [('r6a', list(range(8)), True, 0)]; w = apply_all(w, st); steps += st
    assert w == C
    return l, steps

def D8():
    W = (N(a), N(h), X(a, h))
    l = tuple(reversed(W)) + (Kab, Kef, X(d, e), Kef, Kab) + W
    steps, w = swaps(l)
    st, w = seg(w, 0, 3, (X(e, h), X(a, e), N(e), N(a), X(e, h))); steps += st
    st, w = seg(w, 10, 13, (X(e, h), N(a), N(e), X(a, e), X(e, h))); steps += st
    # X_eh X_ae Ne Na [X_eh C X_eh] Na Ne X_ae X_eh
    st, w = E(w, 4); steps += st
    st, w = seg(w, 1, 4, (N(a), N(e), X(a, e))); steps += st
    st, w = seg(w, 9, 12, (X(a, e), N(a), N(e))); steps += st
    st = [('r6a', list(range(8)), True, 1)]; w = apply_all(w, st); steps += st
    st, w = E(w, 0); steps += st
    assert w == C, w
    return l, steps

if __name__ == '__main__':
    res = {}
    for nm, fn in (('D0', D0), ('D8', D8)):
        l, st = fn()
        print(nm, len(st))
        res[nm] = (l, st)
    json.dump(res, open(os.path.join(HERE, 'd1223.json'), 'w'))
