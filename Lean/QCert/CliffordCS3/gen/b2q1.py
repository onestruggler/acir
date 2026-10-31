"""Phase C design with the atom on qubit 1: Gray path 6, 4, 0, 2, 3, 1, 5, 7, atoms Z = i_[7],
K = K_[5,7] (K on qubit 1 controlled by qubits 0 and 2), coset representatives I and
J = i_[7] I.  The decodings, the coset action and the list of three-qubit identities (B2, (a))."""
import numpy as np
from macro import Macro, macro_axioms
from qc import un_mat, eq, key

GRAY = [6, 4, 0, 2, 3, 1, 5, 7]
M8 = Macro(8, GRAY)
STD = {'r1': 7, 'r3': (5, 7), 'r4': (7, 5), 'r6': (1, 5, 7), 'r9': (5, 7, 1, 3), 'r15': (5, 7),
       'r19': (1, 3, 5, 7)}
TOK = {0: 'X2 CCX1 X2', 1: 'X1 X2 CCX0 X2 X1', 2: 'X0 X2 CCX1 X2 X0', 3: 'X0 CCX2 X0',
       4: 'X0 CCX1 X0', 5: 'X1 CCX0 X1', 6: 'CCX1'}


def matrices():
    Z = un_mat(8, ('i', 7))
    Zi = np.linalg.inv(Z)
    K = un_mat(8, ('K', 5, 7))
    tok = {d: M8.mm[('t', d)] for d in range(7)}
    return Z, Zi, K, tok


def define(W, ki_word=None):
    Z, Zi, K, tok = matrices()
    for d, s in TOK.items():
        W.A.define('T%d' % d, tuple(s.split()))
        assert eq(W.A.mats['T%d' % d], tok[d]), d
    W.A.define('T6J', ('CCX1', 'C02', 'CCZ'))
    assert eq(W.A.mats['T6J'], Z @ tok[6] @ Zi)
    if ki_word is None:
        from ctv import word_of
        ki_word = word_of(W.KB1, K @ Zi)
        assert ki_word is not None
    W.A.define('KI', tuple(ki_word))
    assert eq(W.A.mats['KI'], K @ Zi)
    from ctv import word_of
    kj = word_of(W.KB1, Z @ K)
    assert kj is not None
    W.A.define('KJ', tuple(kj))
    return W


def letter_action(c, x):
    if x == 'Z':
        return ((), 'J') if c == 'I' else (('CCZ',), 'I')
    if x == 'K':
        return (('KI',), 'J') if c == 'I' else (('KJ',), 'I')
    d = x[1]
    if c == 'J' and d == 6:
        return (('T6J',), 'J')
    return (('T%d' % d,), c)


def hstarM(c, w):
    out = ()
    for x in w:
        u, c = letter_action(c, x)
        out += u
    return out, c


def b2_list():
    out = []
    for nm, l, r in macro_axioms(M8, STD):
        for c in ('I', 'J'):
            u, cu = hstarM(c, l)
            v, cv = hstarM(c, r)
            assert cu == cv
            out.append((nm, c, u, v))
    return out


FG = {'i': [('i', j) for j in range(8)],
      'K0': [('K', 0, 4), ('K', 1, 5), ('K', 2, 6), ('K', 3, 7)],
      'K1': [('K', 0, 2), ('K', 1, 3), ('K', 4, 6), ('K', 5, 7)],
      'K2': [('K', 0, 1), ('K', 2, 3), ('K', 4, 5), ('K', 6, 7)],
      'S0': [('i', 4), ('i', 5), ('i', 6), ('i', 7)],
      'S1': [('i', 2), ('i', 3), ('i', 6), ('i', 7)],
      'S2': [('i', 1), ('i', 3), ('i', 5), ('i', 7)],
      'C01': [('i', 6), ('i', 7)], 'C12': [('i', 3), ('i', 7)]}


def a_list():
    out = []
    for x, gens in FG.items():
        u, c = hstarM('I', M8.enc_word(gens))
        assert c == 'I'
        out.append((x, u))
    return out
