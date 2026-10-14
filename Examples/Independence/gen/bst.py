"""Bian and Selinger's relations for 2-qubit Clifford+T operators
(Examples.Groups.Clifford+T-2qubit.Generator, Clifford+T.Rel), words in
operator order over W, H0, H1, S0, S1, T0, T1, CZ, and the decoding D
into CliffT₂ on two wires: the word reversed (time order), qubit 0 on
wire 0 (the high bit of their numbering, as of Real-Clifford's), S as
T T, CZ as H CNOT H on wire 0."""

G = ['W', 'H0', 'H1', 'S0', 'S1', 'T0', 'T1', 'CZ']


def w(s):
    return s.split()


def p(s, k):
    return w(s) * k


X0 = w('H0 S0 S0 H0')
X1 = w('H1 S1 S1 H1')
Wi = ['W'] * 7
T0i = ['T0'] * 7
T1i = ['T1'] * 7
S0i = ['S0'] * 3
S1i = ['S1'] * 3
CX0 = w('H0 CZ H0')
CX1 = w('H1 CZ H1')
CH0 = w('S0 H0 T0') + CX0 + T0i + w('H0') + S0i
CH1 = w('S1 H1 T1') + CX1 + T1i + w('H1') + S1i
T1HT1i = w('T1 H1') + T1i

C = {}
for g in G:
    C['comm-W ' + g] = (['W', g], [g, 'W'])
for a, b in [('H0', 'H1'), ('H0', 'S1'), ('H0', 'T1'), ('S0', 'H1'), ('S0', 'S1'),
             ('S0', 'T1'), ('T0', 'H1'), ('T0', 'S1'), ('T0', 'T1')]:
    C['comm-%s-%s' % (a, b)] = ([a, b], [b, a])
C.update({
    'order-W': (['W'] * 8, []),
    'order-H0': (['H0'] * 2, []),
    'order-H1': (['H1'] * 2, []),
    'order-S0': (['S0'] * 4, []),
    'order-S1': (['S1'] * 4, []),
    'order-S0H0': (p('S0 H0', 3), ['W']),
    'order-S1H1': (p('S1 H1', 3), ['W']),
    'order-CZ': (['CZ'] * 2, []),
    'comm-S0-CZ': (w('S0 CZ'), w('CZ S0')),
    'comm-S1-CZ': (w('S1 CZ'), w('CZ S1')),
    'rel-X0-CZ': (X0 + ['CZ'], w('CZ S1 S1') + X0),
    'rel-X1-CZ': (X1 + ['CZ'], w('CZ S0 S0') + X1),
    'rel-CZ-H0-CZ': (w('CZ H0 CZ'), w('S0 H0 CZ S0 H0 S0 S1') + Wi),
    'rel-CZ-H1-CZ': (w('CZ H1 CZ'), w('S1 H1 CZ S1 H1 S1 S0') + Wi),
    'square-T0': (['T0'] * 2, ['S0']),
    'square-T1': (['T1'] * 2, ['S1']),
    'lemma-order-T0X0': ((['T0'] + X0) * 2, ['W']),
    'lemma-order-T1X1': ((['T1'] + X1) * 2, ['W']),
    'comm-T0-CZ': (w('T0 CZ'), w('CZ T0')),
    'swap-T0': (w('H1 CZ H0 H1 CZ H0 T0'), w('T1 H1 CZ H0 H1 CZ H0')),
    'rel-A': (CX1 + T1HT1i + CX1 + X1 + T1HT1i, T1HT1i + CX1 + X1 + T1HT1i + CX1),
    'rel-B': (CX1 + w('T1 H1 T1 H1') + T1i + CX1 + X1 + w('T1 H1') + T1i + ['H1'] + T1i,
              w('T1 H1 T1 H1') + T1i + CX1 + X1 + w('T1 H1') + T1i + ['H1'] + T1i + CX1),
    'rel-C': (CH1 + w('H1 T1') + CH1 + CH0 + w('H0 T0') + CH0,
              CH0 + w('H0 T0') + CH0 + CH1 + w('H1 T1') + CH1),
})

SPELL = {'W': 'w', 'H0': 'H0', 'H1': 'H1', 'S0': 'S0', 'S1': 'S1', 'T0': 'T0', 'T1': 'T1',
         'CZ': 'CZ10'}


def D(word):
    """The decoding, in the transcription notation (tcliff's spellings)."""
    return ' '.join(SPELL[g] for g in reversed(word))


if __name__ == '__main__':
    import sys
    sys.stdout.reconfigure(encoding='utf-8')
    import tcliff
    from circ import parse, same
    for k, (l, r) in C.items():
        print(k, same(parse(D(l)), parse(D(r)), 2))
