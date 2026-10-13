"""G.4 of Blake's paper: Bian and Selinger's 2-qubit Clifford+T
relations, decoded, derived in CliffT₂.

The decoding reads a word of theirs letter for letter (bs2.py: their
words are matrices in operator order, ours in diagram order, and every
gate matrix is symmetric, so no reversal is needed), qubit k on wire k,
S as T², CZ as H CX H on wire 0.  The decoded relations are then the
circuits of the paper's Figure 15 with the two wires exchanged, so the
paper's G.4 applies with every lemma mirrored (derive adds the mirror
of each two-wire lemma): (C18) and (C19) are D.31 and D.32 mirrored,
(C20) is (HTH) read backwards, the Clifford relations are the ports of
Appendix A's A.21–A.24 below, and the rest is a line or two.

Each equation is stated on the decoded letters exactly, so that the
Agda decoding function produces its sides."""
from appendixD import D, LIB, OUT
import bs2
from bs2 import R, text

first = len(OUT)

# A.21–A.24 of Appendix A, in CliffT₂: X and H against CZ.
D('XCZ1⁼', 2, [('X1 H0 CX10 H0', None),
               ('X1 H0 CX10 H0 X1 X1', ['D2⁼']),
               ('H0 CX10 X1 X0 H0', ['D12⁼']),
               ('H0 CX10 X1 H0 Z0', ['H2'])])
D('XCZ0⁼', 2, [('X0 H0 CX10 H0', None),
               ('X0 H1 CX01 H1', ['D10⁼']),
               ('H1 CX01 H1 X0 Z1', ['XCZ1⁼']),
               ('H0 CX10 H0 X0 Z1', ['D10⁼'])])
D('CZH1⁼', 2, [('H0 CX10 H1 H0 H0 CX10 H0', None),
               ('wd H0 CX10 S1 H1 S1 H1 S1 H0 H0 CX10 H0', ['Hs⁼']),
               ('wd S1 H0 CX10 H1 H0 S1 H1 H0 CX10 H0 S1', ['D6S⁼']),
               ('wd S1 H1 H0 H0 CX01 S1 CX01 H1 H0 H0 S1', ['D9⁼', 'D10⁼']),
               ('wd S1 H1 CX01 S1 CX01 H1 S1', ['H2']),
               ('wd S1 H1 CX01 S1 Sd0 S0 CX01 H1 S1', ['T8']),
               ('wd S1 H1 Sd0 CX01 S1 CX01 S0 H1 S1', ['D6S⁼']),
               ('wd S1 H1 Sd0 CX10 S0 CX10 S0 H1 S1', ['D7⁼']),
               ('wd S1 H1 Z1 Sd0 Z0 CX10 Z0 S0 CX10 S0 H1 S1', ['D13⁼', 'T8', 'D6S⁼']),
               ('wd S1 H1 Z1 S0 CX10 Sd0 CX10 S0 H1 S1', ['T8']),
               ('wd S1 H1 S1 S0 CX10 Sd0 CX10 S1 H1 S1 S0', ['D6S⁼']),
               ('wd S1 H1 H0 CX10 H0 S1 H1 S1 S0', ['CZ'])])
D('CZH0⁼', 2, [('H0 CX10 H0 H0 H0 CX10 H0', None),
               ('H1 CX01 H1 H0 H1 CX01 H1', ['D10⁼']),
               ('wd S0 H0 H1 CX01 H1 S0 H0 S0 S1', ['CZH1⁼']),
               ('wd S0 H0 H0 CX10 H0 S0 H0 S0 S1', ['D10⁼'])])

# Their CNOT onto qubit 1, decoded, is ours with the wires exchanged.
D('DCX1⁼', 2, [('H1 H0 CX10 H0 H1', None), ('CX01', ['D9⁼', 'H2'])], mirror=False)

# Their controlled Hadamards, decoded, are ours: CH0 on wire 0, CH1 the
# same under the swap.
CH0 = text(bs2.CH0)
CH1 = text(bs2.CH1)
D('DCH0⁼', 2, [(CH0, None), ('CH', ['H2'])], mirror=False)
SWP = ['sT', 'sH', 'σT′⁼', 'σH′⁼', 'ss']
D('DCH1⁼', 2, [(CH1, None),
               ('S1 H1 T1 CX01 Td1 H1 Sd1', ['H2', 'D9⁼']),
               ('S1 H1 T1 CX01 Td1 H1 Sd1 SW01 SW01', ['ss']),
               ('S1 H1 T1 CX01 Td1 H1 T1^3 SW01 T0^3 SW01', SWP),
               ('S1 H1 T1 CX01 Td1 SW01 H0 Sd0 SW01', SWP),
               ('S1 H1 T1 CX01 T1^4 SW01 T0^3 H0 Sd0 SW01', SWP),
               ('S1 H1 T1 CX01 SW01 Td0 H0 Sd0 SW01', SWP),
               ('S1 H1 SW01 T0 CX10 Td0 H0 Sd0 SW01', SWP),
               ('SW01 S0 H0 T0 CX10 Td0 H0 Sd0 SW01', SWP),
               ('CHd', [])], mirror=False)

NAME = {k: 'D' + k.replace('-', '').replace(' ', '') + '⁼' for k in R}

PERM = [k for k in R if k.startswith('comm-')]
SIMPLE = {
    'order-W': ['w8'], 'order-H0': ['H2'], 'order-H1': ['H2'],
    'order-S0': ['T8'], 'order-S1': ['T8'],
    'order-CZ': ['H2', 'D5⁼'],
    'comm-S1-CZ': ['D6S⁼'],
    'rel-X1-CZ': ['XCZ1⁼'], 'rel-X0-CZ': ['XCZ0⁼'],
    'rel-CZ-H1-CZ': ['CZH1⁼'], 'rel-CZ-H0-CZ': ['CZH0⁼'],
}

for k, (l, r) in R.items():
    if k in ('square-T0', 'square-T1'):
        continue                                # the same letters: Agda's refl
    lines = None
    if k in PERM and k not in ('comm-S0-CZ', 'comm-S1-CZ', 'comm-T0-CZ'):
        lines = [(text(l), None), (text(r), [])]
    elif k in SIMPLE:
        lines = [(text(l), None), (text(r), SIMPLE[k])]
    elif k in ('order-S0H0', 'order-S1H1'):
        q = k[7]
        lines = [(text(l), None),
                 ('w S{0} Sd{0} H{0} Sd{0} S{0} H{0}'.format(q), ['E']),
                 (text(r), ['T8', 'H2'])]
    elif k in ('comm-S0-CZ', 'comm-T0-CZ'):
        g = 'S0' if k == 'comm-S0-CZ' else 'T0'
        g1 = g[0] + '1'
        lines = [(text(l), None),
                 ('%s H1 CX01 H1' % g, ['D10⁼']),
                 ('H1 CX01 H1 %s' % g, ['D6S⁼', 'D6⁼']),
                 (text(r), ['D10⁼'])]
    elif k in ('lemma-order-T0X0', 'lemma-order-T1X1'):
        q = k[-1]
        lines = [(text(l), None),
                 ('T{0} w Td{0} X{0} X{0}'.format(q), ['TX']),
                 (text(r), ['D2⁼', 'T8'])]
    elif k == 'swap-T0':
        lines = [(text(l), None),
                 ('CX01 CX10 T0', ['H2', 'D9⁼']),
                 ('SW01 CX01 T0', ['B']),
                 ('T1 SW01 CX01', ['D6⁼', 'σT′⁼']),
                 ('T1 CX01 CX10', ['B']),
                 (text(r), ['D9⁼', 'H2'])]
    elif k == 'rel-A':
        lines = [(text(l), None),
                 ('CX01 T1 H1 Td1 CXwd T1 H1 Td1', ['DCX1⁼']),
                 ('T1 H1 Td1 CXwd T1 H1 Td1 CX01', ['D31⁼']),
                 (text(r), ['DCX1⁼'])]
    elif k == 'rel-B':
        lines = [(text(l), None),
                 ('CX01 T1 H1 T1 H1 Td1 CXwd T1 H1 Td1 H1 Td1', ['DCX1⁼']),
                 ('T1 H1 T1 H1 Td1 CXwd T1 H1 Td1 H1 Td1 CX01', ['D32⁼']),
                 (text(r), ['DCX1⁼'])]
    elif k == 'rel-C':
        lines = [(text(l), None),
                 ('CHd H1 T1 CHd CH H0 T0 CH', ['DCH0⁼', 'DCH1⁼']),
                 ('CHwd T1 CHd CHw T0 CH', ['σH′⁼', 'sH']),
                 ('CHw T0 CH CHwd T1 CHd', ['HTH']),
                 ('CH H0 T0 CH CHd H1 T1 CHd', ['σH′⁼', 'sH']),
                 (text(r), ['DCH0⁼', 'DCH1⁼'])]
    if lines is None:
        raise SystemExit('no derivation for ' + k)
    D(NAME[k], 2, lines, mirror=False)

# Lemma 19: CNOT and the swap, encoded and decoded.
D('DCX⁼', 2, [('H0 H0 CX10 H0 H0', None), ('CX10', ['H2'])], mirror=False)
D('Dσ⁼', 2, [(text(bs2.w('H0 CZ H0 H1 CZ H1 H0 CZ H0')), None),
             ('CX10 H1 H0 CX10 H0 H1 CX10', ['H2']),
             ('CX10 CX01 CX10', ['D9⁼']),
             ('SW01 CX10 CX10', ['B']),
             ('SW01', ['D5⁼'])], mirror=False)

# ---------------------------------------------------------------------
# One wire: Greylyn's relations at n = 2, decoded (greylyn2.py).
import greylyn2

D('XTX⁼', 1, [('X0 T0 X0', None), ('w Td0 X0 X0', ['TX']), ('w Td0', ['D2⁼'])], mirror=False)
D('XT3⁼', 1, [('X0 T0^3 X0', None),
              ('X0 T0 X0 X0 T0 X0 X0 T0 X0', ['D2⁼']),
              ('w3 Td0 Td0 Td0', ['XTX⁼']),
              ('w3 T0^5', ['T8'])], mirror=False)
D('Hd⁼', 1, [('H0 Sd0 H0', None),
             ('H0 Sd0 wd S0 H0 S0 H0 S0', ['Hs⁼']),
             ('wd S0 H0 S0', ['T8', 'H2'])], mirror=False)
# ω on |0⟩ then on |1⟩ is the scalar ω.
D('Gω⁼', 1, [('X0 T0 X0 T0', None), ('w', ['XTX⁼', 'T8'])], mirror=False)

def xtx(j, k):
    """(X T X)^k with its first j factors merged into X T^j X."""
    return ' '.join(['X0 T0^%d X0' % j] + ['X0 T0 X0'] * (k - j))


GT = greylyn2.text
G1 = {k: 'G' + k.replace('-', '').replace('′', 'p') + '⁼' for k in greylyn2.R}
for k, (l, r) in greylyn2.R.items():
    L, Rt = GT(l), GT(r)
    if k == 'order-ω₀':
        lines = [(L, None)] + [(xtx(j, 8), ['D2⁼']) for j in (3, 5, 7, 8)] + \
                [('', ['T8', 'D2⁼'])]
    elif k == 'order-ω₁':
        lines = [(L, None), (Rt, ['T8'])]
    elif k == 'order-H':
        lines = [(L, None), (Rt, ['H2'])]
    elif k == 'order-X':
        lines = [(L, None), (Rt, ['D2⁼'])]
    elif k.startswith('comm-ωω'):
        lines = [(L, None), ('w', ['Gω⁼']), (Rt, ['Gω⁼'])]
    elif k in ('swap-Xω', 'swap-Xω′'):
        lines = [(L, None), (Rt, ['D2⁼'])]
    elif k == 'scalar-X':
        lines = [(L, None), ('w X0', ['Gω⁼']), (Rt, ['Gω⁼'])]
    elif k == 'scalar-H':
        lines = [(L, None), ('w H0', ['Gω⁼']), (Rt, ['Gω⁼'])]
    elif k == 'rel-18':
        lines = [(L, None), (Rt, ['D3⁼'])]
    elif k == 'rel-19':
        lines = [(L, None),
                 ('H0 X0 S0 X0 H0', ['D2⁼']),
                 ('w2 H0 Sd0 H0', ['D4⁼']),
                 ('w S0 H0 S0', ['Hd⁼', 'w8']),
                 ('w9 S0 H0 T0^10', ['w8', 'T8']),
                 ('w6 S0 H0 X0 T0^3 X0 T0^5', ['XT3⁼']),
                 ('X0 T0^6 X0 H0 X0 T0^3 X0 T0^5', ['D4d⁼']),
                 (xtx(4, 6) + ' H0 X0 T0^3 X0 T0^5', ['D2⁼']),
                 (xtx(2, 6) + ' H0 X0 T0^3 X0 T0^5', ['D2⁼']),
                 (xtx(1, 6) + ' H0 X0 T0^3 X0 T0^5', ['D2⁼']),
                 (Rt, ['D2⁼'])]
    D(G1[k], 1, lines, mirror=False)

# Only the new equations go into the module.
del OUT[:first]
