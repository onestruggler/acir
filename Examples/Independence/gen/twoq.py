"""CliffCS₂ on two wires: groundwork for completeness there, which is
open (Clifford+CS.Completeness covers zero, one and three wires).

The source would be Bian and Selinger's two-level relations on four
indices (Clifford+CS-TwoLevel at n = 4), decoded by cs2.py: 118 relation
instances, all checked numerically.  This file derives, from CliffCS₂'s
two-wire axioms alone, the calculus they would need
(Clifford+CS.TwoWire).

The two wires split into two commuting worlds, x₀ = 1 and x₀ = 0.  In
the first, s = CS is the controlled S and t = A = H1 CS H1 the
controlled H S H, z = S0 the controlled i; in the second, B = S1 CS³ is
S controlled by x₀ = 0 (the phase i_[1]) and H1 B H1 its H S H.  (CE) is
exactly the statement that A and B commute (AB); conjugating by H1 makes
H1 B H1 commute with s, and the diagonal gates commute among themselves
(E3, E4), so the two worlds commute.  The CNOT from wire 0 is A², and
it conjugates s to s³ z (CXCS: s = X0 B X0, and A² commutes with B);
the controlled K is CK01 = s t s z³, and CK01² = z³ (CK2).

What is missing: every relation of the canonical pair (2, 3) follows
from the world's braid relation s t s = t s t and (s t)³ = z (K = s t s z³
gives K² = z³, K s² = t² K by the braid alone, K s³ = s K s K), and the
other pairs by conjugation.  Neither was found by search (depth 7,
200 000 states, from the axioms and the lemmas here); (E) on wire 1
only gives H1 = ω⁷ (s t s)(s′ t′ s′) with the other world's s′, t′, which
ties the two worlds' braid defects together without separating them.
Nor is there an obvious counter-model: of some 10 000 two-qubit
Clifford+CS matrices, only ±CS satisfy the two-wire axioms in place of
CS (with H, S standard)."""
import appendixE
from appendixE import D, LIB, OUT
from cs2 import CK01, CK10

first = len(OUT)

C3 = 'CS01 CS01 CS01'
Q = 'CS01 H1 CS01 H1 CS01'          # CK01 without its phase S0³
B = 'S1 CS01 CS01 CS01'              # i_[1]


def T(name, width, lines, **kw):
    D(name, width, lines, mirror=False, **kw)


# ---------------------------------------------------------------------
# One wire.

T('XX⁼', 1, [('X0 X0', None), ('H0 S0 S0 S0 S0 H0', ['H2']), ('', ['S4', 'H2'])])
T('XS⁼', 1, [('X0 S0 X0', None),
             ('w H0 S0 S0 Sd0 H0 Sd0 S0 S0 H0', ['E']),
             ('w H0 S0 H0 S0 H0', ['S4']),
             ('w2 Sd0 H0 Sd0 S0 H0', ['E']),
             ('w2 Sd0', ['S4', 'H2'])])
T('XS3⁼', 1, [('X0 S0 S0 S0 X0', None), ('X0 S0 X0 X0 S0 X0 X0 S0 X0', ['XX⁼']),
              ('w6 S0 S0 S0 S0 S0 S0 S0 S0 S0', ['XS⁼']), ('w6 S0', ['S4'])])

# ---------------------------------------------------------------------
# X and the phases.

T('XD1⁼', 2, [('X1 CS01 X1', None), (C3 + ' X1 S0 X1', ['XCS']), (C3 + ' S0', ['XX⁼'])])
T('XD0⁼', 2, [('X0 CS01 X0', None), (C3 + ' X0 S1 X0', ['XCS↓⁼']), (C3 + ' S1', ['XX⁼'])])
T('XD0′⁼', 2, [('CS01', None), ('X0 X0 CS01 X0 X0', ['XX⁼']),
               ('X0 ' + C3 + ' S1 X0', ['XD0⁼']), ('X0 S1 ' + C3 + ' X0', ['E3⁼'])])
T('XD1c⁼', 2, [('X1 ' + C3 + ' X1', None),
               ('X1 CS01 X1 X1 CS01 X1 X1 CS01 X1', ['XX⁼']),
               (C3 + ' S0 ' + C3 + ' S0 ' + C3 + ' S0', ['XD1⁼']),
               ('CS01 S0 S0 S0', ['E4⁼', 'E2⁼'])])

# ---------------------------------------------------------------------
# (CE): A commutes with B.

T('AB⁼', 2, [(B + ' H1 CS01 H1', None),
             (B + ' H1 CS01 H1 CS01 ' + C3, ['E2⁼']),
             (C3 + ' S1 H1 CS01 H1 CS01 ' + C3, ['E3⁼']),
             (C3 + ' CS01 H1 CS01 H1 S1 ' + C3, ['CE']),
             ('H1 CS01 H1 ' + B, ['E2⁼'])])
T('A2B⁼', 2, [(B + ' CX01', None),
              (B + ' H1 CS01 H1 H1 CS01 H1', ['H2']),
              ('H1 CS01 H1 H1 CS01 H1 ' + B, ['AB⁼']),
              ('CX01 ' + B, ['H2'])])
T('A2B′⁼', 2, [('S1 S1 S1 CS01 CX01', None),
               (B + ' ' + B + ' ' + B + ' CX01', ['E3⁼', 'E2⁼']),
               ('CX01 ' + B + ' ' + B + ' ' + B, ['A2B⁼']),
               ('CX01 S1 S1 S1 CS01', ['E3⁼', 'E2⁼'])])

# ---------------------------------------------------------------------
# The CNOT from wire 0.

T('XtCX⁼', 2, [('X1 CX01', None), ('H1 S1 S1 CS01 CS01 H1', ['H2']),
               ('H1 CS01 CS01 S1 S1 H1', ['E3⁼']), ('CX01 X1', ['H2'])])
T('XcCX⁼', 2, [('X0 CX01 X0', None),
               ('H1 X0 CS01 X0 X0 CS01 X0 H1', ['XX⁼']),
               ('H1 ' + C3 + ' S1 ' + C3 + ' S1 H1', ['XD0⁼']),
               ('H1 CS01 CS01 S1 S1 H1', ['E3⁼', 'E2⁼']),
               ('CX01 X1', ['H2'])])
T('S0CX⁼', 2, [('S0 CX01', None), ('H1 CS01 CS01 S0 H1', ['E4⁼']), ('CX01 S0', [])])
T('CXCS⁼', 2, [('CX01 CS01 CX01', None),
               ('CX01 X0 S1 ' + C3 + ' X0 CX01', ['XD0′⁼']),
               ('X0 X0 CX01 X0 S1 ' + C3 + ' X0 CX01 X0 X0', ['XX⁼']),
               ('X0 CX01 X1 S1 ' + C3 + ' CX01 X1 X0', ['XcCX⁼']),
               ('X0 CX01 X1 S1 ' + C3 + ' X1 CX01 X0', ['XtCX⁼']),
               ('X0 CX01 X1 S1 X1 X1 ' + C3 + ' X1 CX01 X0', ['XX⁼']),
               ('X0 CX01 w2 S1 S1 S1 CS01 S0 S0 S0 CX01 X0', ['XS⁼', 'XD1c⁼']),
               ('X0 CX01 w2 S1 S1 S1 S0 S0 S0 CS01 CX01 X0', ['E4⁼']),
               ('X0 w2 S0 S0 S0 CX01 S1 S1 S1 CS01 CX01 X0', ['S0CX⁼']),
               ('X0 w2 S0 S0 S0 S1 S1 S1 CS01 CX01 CX01 X0', ['A2B′⁼']),
               ('X0 w2 S0 S0 S0 S1 S1 S1 CS01 X0', ['CXCX↓⁼']),
               ('w2 X0 S0 S0 S0 X0 S1 S1 S1 X0 CS01 X0', ['XX⁼']),
               ('w8 S0 S1 S1 S1 ' + C3 + ' S1', ['XS3⁼', 'XD0⁼']),
               ('w8 S0 S1 S1 S1 S1 ' + C3, ['E3⁼']),
               (C3 + ' S0', ['w8', 'S4', 'E4⁼'])])

# ---------------------------------------------------------------------
# The controlled K: CK01 = c A c S0³.

T('S0Q⁼', 2, [('S0 ' + Q, None), (Q + ' S0', ['E4⁼'])])
T('CK2⁼', 2, [(CK01 + ' ' + CK01, None),
              (Q + ' ' + Q + ' S0 S0 S0 S0 S0 S0', ['S0Q⁼']),
              ('CS01 H1 CS01 CX01 CS01 H1 CS01 S0 S0', ['S4']),
              ('CS01 H1 CS01 CX01 CS01 CX01 CX01 H1 CS01 S0 S0', ['CXCX↓⁼']),
              ('CS01 H1 CS01 CS01 CS01 CS01 S0 CX01 H1 CS01 S0 S0', ['CXCS⁼']),
              ('CS01 H1 S0 CX01 H1 CS01 S0 S0', ['E2⁼']),
              ('S0 CS01 H1 CX01 H1 CS01 S0 S0', ['E4⁼']),
              ('S0 CS01 CS01 CS01 CS01 S0 S0', ['H2']),
              ('S0 S0 S0', ['E2⁼'])])
T('BQ⁼', 2, [(B + ' ' + Q, None), (Q + ' ' + B, ['AB⁼', 'E3⁼', 'E2⁼'])])
T('BS0⁼', 2, [(B + ' S0', None), ('S0 ' + B, ['E4⁼'])])
T('BCK⁼', 2, [(B + ' ' + CK01, None), (Q + ' ' + B + ' S0 S0 S0', ['BQ⁼']),
              (CK01 + ' ' + B, ['BS0⁼'])])

# Only the new equations go into the module.
del OUT[:first]
