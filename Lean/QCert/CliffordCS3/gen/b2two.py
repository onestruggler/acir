"""Phase A: two-qubit completeness of the fragment (a)-(c) of Figure 2, by the
Reidemeister–Schreier theorem from Bian–Selinger's presentation of U4(Z[1/2,i]) (one coset).

The coset action is h(y) = D(enc(y)): the encoding `enc` of a two-level generator as a macro
word (Gray tokens t0 = (1 0), t1 = (0 2), t2 = (2 3), atoms Z = i_[3], K = K_[2,3]) and the
decoding D of the macro letters as circuits (T0, T1, T2, CS, KA).  Hypothesis (b) splits into
B1 (every relation instance is derivable over the macro alphabet; combinatorial) and B2 (every
macro axiom decodes to a derivable equation, proved here), hypothesis (a) is `prove_a`.
"""
import numpy as np
import two
from macro import Macro, macro_axioms
from qc import eq
from table import Deriv
from ctv import word_of

T = lambda d: ('t', d)
M4 = Macro(4, [1, 0, 2, 3], frames={(1, 3): [T(0), T(1), T(0)]})
STD4 = {'r1': 3, 'r3': (2, 3), 'r4': (3, 2), 'r6': (1, 2, 3), 'r9': (2, 3, 0, 1), 'r15': (2, 3),
        'r19': (0, 1, 2, 3)}
DEC4 = {'T0': ('i', 'Kl', 'Sl', 'Sl', 'CS', 'CS', 'Kl'), 'T1': ('i', 'Ku', 'Su', 'Su', 'CS', 'CS', 'Ku'),
        'T2': ('i', 'Kl', 'CS', 'CS', 'Kl'), 'KA': ('i', 'Su', 'Su', 'Su', 'CS', 'Kl', 'CS', 'Kl', 'CS')}
MLET = {('t', 0): 'T0', ('t', 1): 'T1', ('t', 2): 'T2', 'Z': 'CS', 'K': 'KA'}
# hypothesis (a): the translation of the generators (basis index 2 u + l)
F2 = {'i': [('i', 0), ('i', 1), ('i', 2), ('i', 3)], 'Ku': [('K', 0, 2), ('K', 1, 3)],
      'Kl': [('K', 0, 1), ('K', 2, 3)], 'Su': [('i', 2), ('i', 3)], 'Sl': [('i', 1), ('i', 3)],
      'CS': [('i', 3)]}


def dec(mw):
    return tuple(MLET[x] for x in mw)


def build(verbose=False):
    W = two.build(DEC4, verbose)
    for nm in DEC4:
        assert eq(W.A.mats[nm], M4.mm[[k for k, v in MLET.items() if v == nm][0]])
    for x in ['T0', 'T1', 'T2', 'CXb']:
        e = W.prove((x, x), ())
        W.add_inverse(x, (x,), e, e)
    D0 = W.Au.H
    perms = ['Xu', 'Xl', 'T0', 'T1', 'T2', 'CXb']
    rel = []
    for P in perms:
        for x in ['i', 'Su', 'Sl', 'CS']:
            m = W.A.mats[P] @ W.A.mats[x] @ np.linalg.inv(W.A.mats[P])
            h = D0.word(D0.exps(m))
            rel.append(W.prove((P, x), h + (P,)))
    R, order = two.min_rules(perms, W.A.mats)
    for u, v in R:
        rel.append(W.prove(u, v))
    W.add_group('M2', ['i', 'Su', 'Sl', 'CS'] + perms, D0, rel)
    for name, L, X in [('AlX', ['i', 'Su', 'Sl', 'CS', 'Kl', 'Xu'], 'Xu'),
                       ('AuX', ['i', 'Su', 'Sl', 'CS', 'Ku', 'Xl'], 'Xl')]:
        G0 = W.Al if X == 'Xu' else W.Au
        rel = list(G0.relators)
        for x in L[:-1]:
            m = W.A.mats[X] @ W.A.mats[x] @ np.linalg.inv(W.A.mats[X])
            rel.append(W.prove((X, x), word_of(G0, m) + (X,)))
        rel.append(W.inv.right[X][0])
        W.add_group(name, L, D0, rel)
    e = two.prove_any(W, ('SW', 'SW'), ())
    W.add_inverse('SW', ('SW',), e, e)
    return W


def prove_PQ(W):
    """E01 E23 = Kl and E02 E13 = Ku (E02 = SW E01 SW, E13 = SW E23 SW)."""
    if hasattr(W, 'PQ'):
        return W.PQ
    E = {pq: dec(M4.E(*pq)) for pq in [(0, 1), (2, 3), (0, 2), (1, 3)]}
    P = E[(0, 1)] + E[(2, 3)]
    eP = two.prove_any(W, P, ('Kl',))
    Q = E[(0, 2)] + E[(1, 3)]
    D = Deriv(W.T, Q)
    two.rewrite(W, D, 0, len(E[(0, 2)]), ('SW',) + E[(0, 1)] + ('SW',))
    k = 2 + len(E[(0, 1)])
    two.rewrite(W, D, k, len(D.w), ('SW',) + E[(2, 3)] + ('SW',))
    D.step(k - 1, W.inv.right['SW'][0], True)
    D.step(1, eP, True)
    two.rewrite(W, D, 0, 3, ('Ku',))
    eQ = W.T.derived(Q, ('Ku',), D.steps)
    W.PQ = (eP, eQ)
    return W.PQ


def prove_r19(W):
    """r19 at (0,1,2,3): E01 E23 E02 E13 = E02 E13 E01 E23, through prove_PQ."""
    eP, eQ = prove_PQ(W)
    E = {pq: dec(M4.E(*pq)) for pq in [(0, 1), (2, 3), (0, 2), (1, 3)]}
    lhs = E[(0, 1)] + E[(2, 3)] + E[(0, 2)] + E[(1, 3)]
    rhs = E[(0, 2)] + E[(1, 3)] + E[(0, 1)] + E[(2, 3)]
    D = Deriv(W.T, lhs)
    D.step(0, eP, True)
    D.step(1, eQ, True)
    D.step(0, W.ax['comm_Ku_Kl'], False)
    D.step(1, eP, False)
    D.step(0, eQ, False)
    assert D.w == rhs
    return W.T.derived(lhs, rhs, D.steps)


def prove_b2(W, verbose=False):
    out = {}
    for nm, l, r in macro_axioms(M4, STD4):
        if nm == 'r19':
            e = prove_r19(W)
        else:
            e = two.prove_any(W, dec(l), dec(r))
        out[nm] = (dec(l), dec(r), e)
        if verbose:
            print(' B2', nm, W.T.size(e) if e is not None else 0)
    return out


def prove_a(W, verbose=False):
    out = {}
    for x, gens in F2.items():
        w = dec(M4.enc_word(gens))
        if x == 'Ku':
            e = prove_PQ(W)[1]
        elif x == 'Kl':
            e = prove_PQ(W)[0]
        else:
            e = two.prove_any(W, w, (x,))
        out[x] = (w, (x,), e)
        if verbose:
            print(' a', x, W.T.size(e) if e is not None else 0)
    return out


if __name__ == '__main__':
    import time
    t = time.time()
    W = build(True)
    prove_b2(W, True)
    prove_a(W, True)
    print('time %.1f' % (time.time() - t), 'eqs', len(W.T.eqs),
          'steps', sum(W.T.size(i) for i in range(len(W.T.eqs))))
