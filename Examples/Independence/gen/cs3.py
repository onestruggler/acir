"""Bian and Selinger's relations for 3-qubit Clifford+CS operators
(Examples.Groups.Clifford+CS-3qubit.Theorem, module CliffordCS), words
over iI, S0–S2, K0–K2, CS01, CS12, and the decoding into CliffCS₂: their
qubit k on wire k, K as ω† H (K = (1 + i)⁻¹ [[1, 1], [1, −1]] = ω⁻¹ H),
the scalar i as ω², letter for letter (every gate matrix is symmetric,
so no reversal is needed)."""

GENS = ['iI', 'S0', 'S1', 'S2', 'K0', 'K1', 'K2', 'CS01', 'CS12']


def w(s):
    return s.split()


def pw(word, k):
    return word * k


iI, S0, S1, S2, K0, K1, K2, CS01, CS12 = [[g] for g in GENS]
X0 = K0 + S0 + S0 + K0 + iI
X1 = K1 + S1 + S1 + K1 + iI
X2 = K2 + S2 + S2 + K2 + iI
CX01 = K1 + CS01 + CS01 + K1 + iI
CX12 = K2 + CS12 + CS12 + K2 + iI
CX21 = K1 + CS12 + CS12 + K1 + iI
# CS10 and CS21 are CS01 and CS12 (the original's synonyms).
CX10 = K0 + CS01 + CS01 + K0 + iI

R = {}
for g in ['S0', 'S1', 'S2', 'K0', 'K1', 'K2', 'CS01', 'CS12']:
    R['ax-iI-%s=%s-iI' % (g, g)] = (['iI', g], [g, 'iI'])
R['ax-iI-iI-iI-iI=ε'] = (pw(iI, 4), [])
for a, b in [('S1', 'S0'), ('S2', 'S0'), ('S2', 'S1'), ('K1', 'K0'), ('K2', 'K0'), ('K2', 'K1'),
             ('CS01', 'S0'), ('CS12', 'S0'), ('CS01', 'S1'), ('CS12', 'S1'), ('CS01', 'S2'),
             ('CS12', 'S2'), ('CS12', 'CS01'), ('S1', 'K0'), ('S2', 'K0'), ('S2', 'K1'),
             ('K1', 'S0'), ('K2', 'S0'), ('K2', 'S1'), ('CS01', 'K2'), ('CS12', 'K0')]:
    R['ax-%s-%s=%s-%s' % (a, b, b, a)] = ([a, b], [b, a])
for g in ['S0', 'S1', 'S2', 'CS01', 'CS12']:
    R['ax-%s-%s-%s-%s=ε' % (g, g, g, g)] = (pw([g], 4), [])
for k in '012':
    R['ax-K%s-K%s=iI-iI-iI' % (k, k)] = (pw(['K' + k], 2), pw(iI, 3))
    R['ax-S%s-K%s-S%s-K%s-S%s-K%s=iI-iI-iI' % ((k,) * 6)] = (pw(['S' + k, 'K' + k], 3), pw(iI, 3))
R['ax-X0-CS01=CS01-CS01-CS01-X0-S1'] = (X0 + CS01, pw(CS01, 3) + X0 + S1)
R['ax-X1-CS01=CS01-CS01-CS01-X1-S0'] = (X1 + CS01, pw(CS01, 3) + X1 + S0)
R['ax-X1-CS12=CS12-CS12-CS12-X1-S2'] = (X1 + CS12, pw(CS12, 3) + X1 + S2)
R['ax-X2-CS12=CS12-CS12-CS12-X2-S1'] = (X2 + CS12, pw(CS12, 3) + X2 + S1)
for c, k in [('CS01', '0'), ('CS01', '1'), ('CS12', '1'), ('CS12', '2')]:
    K, S = ['K' + k], ['S' + k]
    R['ax-%s-K%s-%s-K%s-S%s=S%s-K%s-%s-K%s-%s' % (c, k, c, k, k, k, k, c, k, c)] = (
        [c] + K + [c] + K + S, S + K + [c] + K + [c])
R['ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12'] = (
    CX10 + CX01 + CS12 + CX01 + CX10, CX12 + CX21 + CS01 + CX21 + CX12)
R['ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12'] = (
    CX10 + CX01 + CS12 + CS12 + CX01 + CX10, CX01 + CS12 + CS12 + CX01 + CS12 + CS12)
R['ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21'] = (
    CS12 + CX01 + pw(CS12, 3) + CX01, CS01 + CX21 + pw(CS01, 3) + CX21)
R['ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12'] = (
    CS12 + K1 + CS12 + K1 + CS01 + K1 + CS01, CS01 + K1 + CS01 + K1 + CS12 + K1 + CS12)
R['ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1'] = (
    CS12 + K1 + pw(CS12, 3) + K1 + CS01 + K1 + CS12,
    CS01 + K1 + pw(CS01, 3) + K1 + CS12 + K1 + CS01)

DEC = {'iI': 'w w', 'S0': 'S0', 'S1': 'S1', 'S2': 'S2', 'K0': 'wd H0', 'K1': 'wd H1',
       'K2': 'wd H2', 'CS01': 'CS01', 'CS12': 'CS12'}


def text(word):
    return ' '.join(DEC[x] for x in word)
