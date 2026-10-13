"""Bian and Selinger's relations for 2-qubit Clifford+T operators
(Examples.Groups.Clifford+T-2qubit.Generator, module Clifford+T),
words over W, H0, H1, S0, S1, T0, T1, CZ, and the decoding into
CliffT₂: their qubit k our wire k, S read as T², CZ as H CX H on
wire 0."""

GENS = ['W', 'H0', 'H1', 'S0', 'S1', 'T0', 'T1', 'CZ']


def w(s):
    return s.split()


def pw(word, k):
    """word ^ k, as Word.Base spells it (letters only)."""
    return word * k


X0 = w('H0 S0 S0 H0')
X1 = w('H1 S1 S1 H1')
Wi = pw(['W'], 7)
T0i, T1i = pw(['T0'], 7), pw(['T1'], 7)
S0i, S1i = pw(['S0'], 3), pw(['S1'], 3)
CX0 = w('H0 CZ H0')
CX1 = w('H1 CZ H1')
CH0 = ['S0', 'H0', 'T0'] + CX0 + T0i + ['H0'] + S0i
CH1 = ['S1', 'H1', 'T1'] + CX1 + T1i + ['H1'] + S1i

R = {}
for g in GENS:
    R['comm-W ' + g] = (['W', g], [g, 'W'])
for a, b in [('H0', 'H1'), ('H0', 'S1'), ('H0', 'T1'), ('S0', 'H1'), ('S0', 'S1'),
             ('S0', 'T1'), ('T0', 'H1'), ('T0', 'S1'), ('T0', 'T1')]:
    R['comm-%s-%s' % (a, b)] = ([a, b], [b, a])
R['order-W'] = (pw(['W'], 8), [])
R['order-H0'] = (pw(['H0'], 2), [])
R['order-H1'] = (pw(['H1'], 2), [])
R['order-S0'] = (pw(['S0'], 4), [])
R['order-S1'] = (pw(['S1'], 4), [])
R['order-S0H0'] = (pw(['S0', 'H0'], 3), ['W'])
R['order-S1H1'] = (pw(['S1', 'H1'], 3), ['W'])
R['order-CZ'] = (pw(['CZ'], 2), [])
R['comm-S0-CZ'] = (w('S0 CZ'), w('CZ S0'))
R['comm-S1-CZ'] = (w('S1 CZ'), w('CZ S1'))
R['rel-X0-CZ'] = (X0 + ['CZ'], w('CZ S1 S1') + X0)
R['rel-X1-CZ'] = (X1 + ['CZ'], w('CZ S0 S0') + X1)
R['rel-CZ-H0-CZ'] = (w('CZ H0 CZ'), w('S0 H0 CZ S0 H0 S0 S1') + Wi)
R['rel-CZ-H1-CZ'] = (w('CZ H1 CZ'), w('S1 H1 CZ S1 H1 S1 S0') + Wi)
R['square-T0'] = (pw(['T0'], 2), ['S0'])
R['square-T1'] = (pw(['T1'], 2), ['S1'])
R['lemma-order-T0X0'] = (pw(['T0'] + X0, 2), ['W'])
R['lemma-order-T1X1'] = (pw(['T1'] + X1, 2), ['W'])
R['comm-T0-CZ'] = (w('T0 CZ'), w('CZ T0'))
R['swap-T0'] = (w('H1 CZ H0 H1 CZ H0 T0'), w('T1 H1 CZ H0 H1 CZ H0'))
R['rel-A'] = (CX1 + ['T1', 'H1'] + T1i + CX1 + X1 + ['T1', 'H1'] + T1i,
              ['T1', 'H1'] + T1i + CX1 + X1 + ['T1', 'H1'] + T1i + CX1)
R['rel-B'] = (CX1 + w('T1 H1 T1 H1') + T1i + CX1 + X1 + w('T1 H1') + T1i + ['H1'] + T1i,
              w('T1 H1 T1 H1') + T1i + CX1 + X1 + w('T1 H1') + T1i + ['H1'] + T1i + CX1)
R['rel-C'] = (CH1 + w('H1 T1') + CH1 + CH0 + w('H0 T0') + CH0,
              CH0 + w('H0 T0') + CH0 + CH1 + w('H1 T1') + CH1)

DEC = {'W': 'w', 'H0': 'H0', 'H1': 'H1', 'S0': 'T0 T0', 'S1': 'T1 T1', 'T0': 'T0',
       'T1': 'T1', 'CZ': 'H0 CX10 H0'}


def text(word):
    """The decoding of a word: each letter replaced, in the same order.

    Their words are read as matrices in operator order, ours in diagram
    order; every gate matrix being symmetric, reading a word in the
    other order transposes its matrix, so the decoding need not reverse
    (the bridge compares with the transpose instead), and the decoded
    relations are the circuits of the paper's Figure 15 (with the wires
    exchanged: their qubit k is our wire k)."""
    return ' '.join(DEC[x] for x in word)
