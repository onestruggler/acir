"""The relations of the canonical pair (2, 3) on two wires, decoded:
K = CK01 = s t s z³ (s = CS, t = H1 CS H1, z = S0), X = CX01 = t²,
i₃ = s and i₂ = X1 s X1, derived from the braid s t s = t s t and
(s t s)² = z (twoq.py)."""
import twoq
from twoq import T, dnorm, deq, C3, Q, B
from appendixE import OUT
from cs2 import CK01

first = len(OUT)
t = 'H1 CS01 H1'
Z3 = 'S0 S0 S0'
I2 = 'X1 CS01 X1'

# s³ t s = t s t³, and s CX s = z CX.
T('BRI⁼', 2, [(C3 + ' ' + t + ' CS01', None),
              (C3 + ' ' + t + ' CS01 ' + t + ' H1 ' + C3 + ' H1', ['H2', 'E2⁼']),
              (C3 + ' CS01 ' + t + ' CS01 H1 ' + C3 + ' H1', ['braid⁼']),
              (t + ' CS01 H1 ' + C3 + ' H1', ['E2⁼'])])
T('sXs⁼', 2, [('CS01 CX01 CS01', None),
              ('CX01 CX01 CS01 CX01 CS01', ['CXCX↓⁼']),
              ('CX01 ' + C3 + ' S0 CS01', ['CXCS⁼']),
              ('S0 CX01', ['E4⁼', 'E2⁼', 'S0CX⁼'])])
# t z = s t s³ t s.
T('TZ⁼', 2, [('CS01 ' + t + ' ' + C3 + ' ' + t + ' CS01', None),
             ('CS01 ' + t + ' ' + t + ' CS01 H1 ' + C3 + ' H1', ['BRI⁼']),
             ('CS01 CX01 CS01 H1 ' + C3 + ' H1', ['H2']),
             ('S0 CX01 H1 ' + C3 + ' H1', ['sXs⁼']),
             ('S0 ' + t, ['H2', 'E2⁼'])])

# (13): K s² = X K.
T('C13⁼', 2, [(CK01 + ' CS01 CS01', None),
              (Q + ' CS01 CS01 ' + Z3, ['E4⁼']),
              (t + ' CS01 ' + t + ' CS01 CS01 ' + Z3, ['braid⁼']),
              (t + ' ' + t + ' CS01 ' + t + ' CS01 ' + Z3, ['braid⁼']),
              ('CX01 ' + CK01, ['H2'])])
# (14): K s³ = s K s K.
T('S0Q2⁼', 2, [('S0 CS01 CS01 ' + t + ' CS01', None), ('CS01 CS01 ' + t + ' CS01 S0', ['E4⁼'])])
T('C14⁼', 2, [(CK01 + ' ' + C3, None),
              ('CS01 ' + t + ' ' + Z3, ['E4⁼', 'E2⁼']),
              ('S0 S0 CS01 S0 ' + t, ['E4⁼']),
              ('S0 S0 CS01 CS01 ' + t + ' ' + C3 + ' ' + t + ' CS01', ['TZ⁼']),
              ('CS01 CS01 ' + t + ' ' + C3 + ' ' + t + ' CS01 S0 S0', ['S0Q2⁼']),
              ('CS01 CS01 ' + t + ' ' + C3 + ' ' + t + ' CS01 S0 S0 S0 S0 S0 S0', ['S4']),
              ('CS01 CS01 ' + t + ' CS01 S0 S0 S0 CS01 CS01 ' + t + ' CS01 S0 S0 S0', ['S0Q2⁼']),
              ('CS01 ' + CK01 + ' CS01 ' + CK01, [])], maxstates=40000)
# (15): K passes i₂ i₃ = z.
T('i2i3⁼', 2, [(I2 + ' CS01', None), (C3 + ' S0 CS01', ['XD1⁼']), ('S0', ['E4⁼', 'E2⁼'])])
T('C15⁼', 2, [(CK01 + ' ' + I2 + ' CS01', None), (CK01 + ' S0', ['i2i3⁼']),
              ('S0 ' + CK01, ['S0Q⁼']), (I2 + ' CS01 ' + CK01, ['i2i3⁼'])])
# (16): K² i₂ i₃ = ε.
T('C16⁼', 2, [(CK01 + ' ' + CK01 + ' ' + I2 + ' CS01', None), (Z3 + ' S0', ['CK2⁼', 'i2i3⁼']),
              ('', ['S4'])])
# (1)–(3) at the canonical pair.
T('CK8⁼', 2, [(' '.join([CK01] * 8), None), (' '.join([Z3] * 4), ['CK2⁼']), ('', ['S4'])])
# (10): i₃ X = X i₂.
T('C10⁼', 2, [('CS01 CX01', None), ('CX01 CX01 CS01 CX01', ['CXCX↓⁼']),
              ('CX01 ' + C3 + ' S0', ['CXCS⁼']), ('CX01 ' + I2, ['XD1⁼'])])

del OUT[:first]
