"""The canonical instances of the two-level relations on four indices
that relate two pairs (the commutations, the exchanges, (19)), in the
frame of the pair (2, 3), and the transports of single generators by one
permutation gate that the frames are built of (cs2.FRAME)."""
import w2perm
import cliffsub
from twoq import T, dnorm, deq, C3, Q, B, TB, B3
from appendixE import OUT
from cs2 import CK01, FRAME, IFRAME, conj, DI, DX, DK

first = len(OUT)
t = 'H1 CS01 H1'
I0, I1, I2 = DI[0], DI[1], DI[2]
N = 'X0 CX01 X0'
NF0 = 'w2 S0 S0 S0 S1 S1 S1 CS01'            # i₀, diagonal

# ---------------------------------------------------------------------
# The phases, diagonal.

T('iD1⁼', 2, [(I1, None), (C3 + ' S1', ['XD0⁼']), (B, ['E3⁼'])])
T('iD2⁼', 2, [(I2, None), (C3 + ' S0', ['XD1⁼'])])
T('iD0⁼', 2, [(I0, None),
              ('X0 ' + C3 + ' S0 X0', ['XD1⁼']),
              ('X0 CS01 X0 X0 CS01 X0 X0 CS01 X0 X0 S0 X0', ['XX⁼']),
              (C3 + ' S1 ' + C3 + ' S1 ' + C3 + ' S1 w2 S0 S0 S0', ['XD0⁼', 'XS⁼'])]
  + dnorm(C3 + ' S1 ' + C3 + ' S1 ' + C3 + ' S1 w2 S0 S0 S0'))
# i₀ is z³ B³ ω².
T('iD0B⁼', 2, [(NF0, None)] + deq(NF0, 'w2 S0 S0 S0 ' + B3))

# ---------------------------------------------------------------------
# The other world: N = X0 CX01 X0 is H1 B² H1, and t′ = H1 B H1 passes
# t, hence the controlled K; and the controlled K on x₀ = 0.

T('NB⁼', 2, [(N, None), ('CX01 X1', ['XcCX⁼']), ('H1 CS01 CS01 S1 S1 H1', ['H2']),
             ('H1 ' + B + ' ' + B + ' H1', ['E3⁼', 'E2⁼', 'SB⁼'])], maxstates=40000)
T('tBt⁼', 2, [(TB + ' ' + t, None), ('H1 ' + B + ' CS01 H1', ['H2']),
              ('H1 CS01 ' + B + ' H1', ['Bc⁼']), (t + ' ' + TB, ['H2'])])
T('tBQ⁼', 2, [(TB + ' ' + Q, None), (Q + ' ' + TB, ['tBc⁼', 'tBt⁼'])])
T('S0TB⁼', 2, [('S0 ' + TB, None), (TB + ' S0', ['E4⁼'])])
T('tBCK⁼', 2, [(TB + ' ' + CK01, None), (Q + ' ' + TB + ' S0 S0 S0', ['tBQ⁼']),
               (CK01 + ' ' + TB, ['S0TB⁼'])])
T('K01W⁼', 2, [(DK[(0, 1)], None),
               ('X0 CS01 X0 H1 X0 CS01 X0 H1 X0 CS01 X0 X0 S0 S0 S0 X0', ['XX⁼']),
               (B + ' H1 ' + B + ' H1 ' + B + ' w6 S0', ['iD1⁼', 'XS3⁼'])])

# ---------------------------------------------------------------------
# Commutations, in the frame of (2, 3).

T('Cii0⁼', 2, [(I0 + ' CS01', None), (NF0 + ' CS01', ['iD0⁼'])]
  + deq(NF0 + ' CS01', 'CS01 ' + NF0) + [('CS01 ' + I0, ['iD0⁼'])])
T('Cii1⁼', 2, [(I1 + ' CS01', None), (B + ' CS01', ['iD1⁼']), ('CS01 ' + B, ['Bc⁼']),
               ('CS01 ' + I1, ['iD1⁼'])])
T('Cii2⁼', 2, [(I2 + ' CS01', None), (C3 + ' S0 CS01', ['iD2⁼']),
               ('CS01 ' + C3 + ' S0', ['E4⁼']), ('CS01 ' + I2, ['iD2⁼'])])
T('CiX1⁼', 2, [(I1 + ' CX01', None), (B + ' CX01', ['iD1⁼']), ('CX01 ' + B, ['A2B⁼']),
               ('CX01 ' + I1, ['iD1⁼'])])
T('CiX0⁼', 2, [(I0 + ' CX01', None), ('w2 S0 S0 S0 ' + B3 + ' CX01', ['iD0⁼', 'iD0B⁼']),
               ('w2 S0 S0 S0 CX01 ' + B3, ['A2B⁼']), ('w2 CX01 S0 S0 S0 ' + B3, ['S0CX⁼']),
               ('CX01 ' + I0, ['iD0⁼', 'iD0B⁼'])])
T('CiK1⁼', 2, [(I1 + ' ' + CK01, None), (B + ' ' + CK01, ['iD1⁼']), (CK01 + ' ' + B, ['BCK⁼']),
               (CK01 + ' ' + I1, ['iD1⁼'])])
T('CiK0⁼', 2, [(I0 + ' ' + CK01, None), ('w2 S0 S0 S0 ' + B3 + ' ' + CK01, ['iD0⁼', 'iD0B⁼']),
               ('w2 S0 S0 S0 ' + CK01 + ' ' + B3, ['BCK⁼']),
               ('w2 ' + CK01 + ' S0 S0 S0 ' + B3, ['S0Q⁼']),
               (CK01 + ' ' + I0, ['iD0⁼', 'iD0B⁼'])])
T('CXX⁼', 2, [(N + ' CX01', None), ('CX01 X1 CX01', ['XcCX⁼']), ('CX01 CX01 X1', ['XtCX⁼']),
              ('CX01 ' + N, ['XcCX⁼', 'XtCX⁼'])])
T('CXK⁼', 2, [(N + ' ' + CK01, None), ('H1 ' + B + ' ' + B + ' H1 ' + CK01, ['NB⁼']),
              (TB + ' ' + TB + ' ' + CK01, ['H2']), (CK01 + ' ' + TB + ' ' + TB, ['tBCK⁼']),
              (CK01 + ' ' + N, ['H2', 'NB⁼'])])
T('CKK⁼', 2, [(DK[(0, 1)] + ' ' + CK01, None),
              (B + ' ' + TB + ' ' + B + ' w6 S0 ' + CK01, ['K01W⁼']),
              ('w6 ' + CK01 + ' ' + B + ' ' + TB + ' ' + B + ' S0', ['BCK⁼', 'tBCK⁼', 'S0Q⁼']),
              (CK01 + ' ' + DK[(0, 1)], ['K01W⁼'])], maxstates=40000)

# ---------------------------------------------------------------------
# (19): K01 K23 = ω⁷ H1, by (E) on wire 1 split between the worlds.

T('SHS⁼', 1, [('S0 H0 S0 H0 S0', None), ('S0 w Sd0 H0 Sd0 S0', ['E']), ('w H0', ['S4'])])
T('KK1⁼', 2, [(DK[(0, 1)] + ' ' + CK01, None),
              (B + ' ' + TB + ' ' + B + ' w6 S0 ' + CK01, ['K01W⁼']),
              ('w6 ' + B + ' ' + TB + ' ' + B + ' ' + Q, ['S0Q⁼', 'S4']),
              ('w6 CS01 ' + B + ' ' + t + ' ' + TB + ' CS01 ' + B, ['BQ⁼', 'tBt⁼', 'Bc⁼', 'tBc⁼']),
              ('w6 S1 H1 S1 H1 S1', ['SB⁼', 'H2']),
              ('w7 H1', ['SHS⁼'])], maxstates=40000)

del OUT[:first]
