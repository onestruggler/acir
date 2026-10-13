"""Appendix D of Blake's paper: auxiliary derivations for CliffT₂.

As appendixA.py: the paper's chains, one line per string, in time
order, wire 0 at the bottom of the figures; T is the only phase gate,
S, S†, Z, X and T† being spelt over it, and the controlled gates of the
figures are the tokens of cliffT.py (CH, CHw, CS, CXw, …).  Where a
lemma is the T-analogue of one of Appendix A's for Cliff₂ (D.5–D.13),
its chain follows appendixA.py's."""
import cliffT
from frag import derive, add_mirror, placed, nat, LIB, OUT
import frag


def D(name, width, lines, **kw):
    derive(name, width, lines, **kw)


# The swap moved the other way.
D('σH′⁼', 2, [('SW01 H0', None), ('H1 SW01', ['sH', 'ss'])])
D('σT′⁼', 2, [('SW01 T0', None), ('T1 SW01', ['sT', 'ss'])])
for n in ['CPh⁼', 'B⁼', 'CZ⁼']:
    add_mirror(n)

# D.1–D.4: one wire.
D('D1⁼', 1, [('Z0 Z0', None), ('', ['T8'])])
D('D2⁼', 1, [('X0 X0', None), ('H0 Z0 Z0 H0', ['H2']), ('H0 H0', ['D1⁼']), ('', ['H2'])])
D('D3⁼', 1, [('H0 X0', None), ('Z0 H0', ['H2'])])
D('D4⁼', 1, [('X0 S0 X0', None),
             ('w H0 S0 S0 Sd0 H0 Sd0 S0 S0 H0', ['E']),
             ('w H0 S0 H0 S0 H0', ['T8']),
             ('w2 Sd0 H0 Sd0 S0 H0', ['E']),
             ('w2 Sd0', ['T8', 'H2'])])
D('D4d⁼', 1, [('X0 Sd0 X0', None),
              ('X0 S0 X0 X0 S0 X0 X0 S0 X0', ['D2⁼']),
              ('w6 Sd0 Sd0 Sd0', ['D4⁼']),
              ('w6 S0', ['T8'])])
D('Hs⁼', 1, [('H0', None), ('H0 Sd0 S0', ['T8']), ('H0 Sd0 H0 H0 S0', ['H2']),
             ('wd S0 H0 S0 H0 S0', ['E'])])
# X and T: (TX) the other way round.
D('XT⁼', 1, [('X0 Td0', None), ('X0 Td0 X0 X0', ['D2⁼']), ('wd X0 X0 T0 X0', ['TX']),
             ('wd T0 X0', ['D2⁼'])])

# D.5: CNOT is an involution.
D('D5⁼', 2, [('CX10 CX10', None),
             ('CX10 CX10 T0 Td0', ['T8']),
             ('CX10 CX10 CX01 T0 CX01 Td0', ['CPh']),
             ('CX10 SW01 CX10 T0 CX01 Td0', ['B']),
             ('CX10 CX01 SW01 T0 CX01 Td0', []),
             ('SW01 CX10 SW01 T0 CX01 Td0', ['B']),
             ('T0 Td0', ['CPh']),
             ('', ['T8'])])

# D.6: T on the control passes the CNOT; and S, S†, T†.
D('D6⁼', 2, [('T1 CX10', None), ('CX10 T1 CX10 CX10', ['CPh']), ('CX10 T1', ['D5⁼'])])
D('D6S⁼', 2, [('S1 CX10', None), ('CX10 S1', ['D6⁼'])])
D('D6d⁼', 2, [('Sd1 CX10', None), ('CX10 Sd1', ['D6S⁼'])])
D('D6t⁼', 2, [('Td1 CX10', None), ('CX10 Td1', ['D6⁼', 'D6d⁼'])])

# D.7, D.8: S and T on the target, between two CNOTs.
D('D7⁼', 2, [('CX10 S0 CX10', None),
             ('SW01 CX01 S1 CX01 SW01', []),
             ('CX01 CX10 S1 CX10 CX01', ['B']),
             ('CX01 S1 CX10 CX10 CX01', ['D6S⁼']),
             ('CX01 S1 CX01', ['D5⁼'])])
D('D7d⁼', 2, [('CX10 Sd0 CX10', None),
              ('CX10 S0 CX10 CX10 S0 CX10 CX10 S0 CX10', ['D5⁼']),
              ('CX01 S1 CX01 CX01 S1 CX01 CX01 S1 CX01', ['D7⁼']),
              ('CX01 Sd1 CX01', ['D5⁼'])])
D('D8⁼', 2, [('CX10 T0 CX10', None),
             ('SW01 CX01 T1 CX01 SW01', []),
             ('CX01 CX10 T1 CX10 CX01', ['B']),
             ('CX01 T1 CX10 CX10 CX01', ['D6⁼']),
             ('CX01 T1 CX01', ['D5⁼'])])
D('D8d⁼', 2, [('CX10 Td0 CX10', None),
              ('CX10 T0 CX10 CX10 Sd0 CX10', ['D5⁼']),
              ('CX01 T1 CX01 CX01 Sd1 CX01', ['D8⁼', 'D7d⁼']),
              ('CX01 Td1 CX01', ['D5⁼'])])
# T on the target passes the diagonal CX T† CX (the steps of D.8 and
# D.6 the paper takes in one).
D('D8c⁼', 2, [('T0 CX10 Td0 CX10', None),
              ('T0 CX01 Td1 CX01', ['D8d⁼']),
              ('CX01 Td1 CX01 T0', ['D6⁼']),
              ('CX10 Td0 CX10 T0', ['D8d⁼'])])

# D.9: H ⊗ H turns a CNOT upside down.
D('D9⁼', 2, [('CX10 H1 H0', None),
             ('H0 H0 CX10 H1 H0', ['H2']),
             ('H0 S1 S0 CX10 Sd0 CX10 H1', ['CZ']),
             ('H0 S1 S0 CX01 Sd1 CX01 H1', ['D7d⁼']),
             ('H0 H1 CX01 H1 H1', ['CZ']),
             ('H0 H1 CX01', ['H2'])])

# D.10: CZ is symmetric.
D('D10⁼', 2, [('H0 CX10 H0', None),
              ('S1 S0 CX10 Sd0 CX10', ['CZ']),
              ('S1 S0 CX01 Sd1 CX01', ['D7d⁼']),
              ('H1 CX01 H1', ['CZ'])])

# D.11: X on the target passes the CNOT.
D('D11⁼', 2, [('X0 CX10', None),
              ('H0 S0 S0 H0 H1 H1 CX10', ['H2']),
              ('H0 S0 S0 H1 CX01 H1 H0', ['D9⁼', 'D10⁼']),
              ('H0 H1 CX01 H1 S0 S0 H0', ['D6S⁼']),
              ('CX10 H1 H1 H0 S0 S0 H0', ['D9⁼', 'D10⁼']),
              ('CX10 X0', ['H2'])])

# D.12: X on the target is X on the control around the CNOT.
D('D12⁼', 2, [('CX10 X0', None),
              ('H0 H0 CX10 H0 H0 X0', ['H2']),
              ('H0 S1 S0 CX10 Sd0 CX10 H0 X0', ['CZ']),
              ('H0 S1 S0 CX01 Sd1 CX01 H0 X0', ['D7d⁼']),
              ('H0 S1 S0 CX01 Sd1 CX01 Z0 H0', ['H2']),
              ('H0 S1 S0 Z0 CX01 Sd1 CX01 H0', ['D6S⁼']),
              ('H0 S1 Sd0 CX01 Sd1 CX01 H0', ['T8']),
              ('w6 H0 S1 Sd0 CX01 X1 S1 X1 CX01 H0', ['w8', 'D4⁼']),
              ('w8 H0 Sd0 X1 Sd1 X1 CX01 X1 S1 X1 CX01 H0', ['w8', 'D4d⁼']),
              ('H0 Sd0 X1 Sd1 X1 CX01 X1 S1 X1 CX01 H0', ['w8']),
              ('X1 Sd1 H0 Sd0 CX01 S1 X1 CX01 H0', ['D11⁼', 'D2⁼']),
              ('X1 Sd1 H0 Sd0 CX01 S1 CX01 X1 H0', ['D11⁼']),
              ('X1 Sd1 H0 Sd0 CX10 S0 CX10 X1 H0', ['D7⁼']),
              ('X1 Sd1 H0 CX10 CX10 Sd0 CX10 S0 CX10 X1 H0', ['D5⁼']),
              ('X1 H0 CX10 Sd1 CX10 Sd0 CX10 S0 CX10 X1 H0', ['D6d⁼']),
              ('X1 H0 CX10 Sd1 CX01 Sd1 CX01 S0 CX10 X1 H0', ['D7d⁼']),
              ('X1 H0 CX10 Sd1 S0 CX01 Sd1 CX01 CX10 X1 H0', ['D6S⁼']),
              ('X1 H0 CX10 Sd1 S0 CX10 Sd0 CX10 CX10 X1 H0', ['D7d⁼']),
              ('X1 H0 CX10 Z1 H0 CX10 H0 CX10 X1 H0', ['CZ', 'T8']),
              ('X1 S1 S0 CX10 Sd0 CX10 Z1 CX10 S1 S0 CX10 Sd0 CX10 X1', ['CZ']),
              ('X1 S0 CX10 Sd0 CX10 CX10 S0 CX10 Sd0 CX10 X1', ['D6S⁼', 'T8']),
              ('X1 S0 CX10 Sd0 S0 CX10 Sd0 CX10 X1', ['D5⁼']),
              ('X1 S0 Sd0 CX10 X1', ['T8', 'D5⁼']),
              ('X1 CX10 X1', ['T8'])])

# D.13: Z on the control is Z on the target around the CNOT.
D('D13⁼', 2, [('CX10 Z1', None),
              ('H1 H0 CX01 H1 H0 Z1', ['D9⁼']),
              ('H1 H0 CX01 X1 H1 H0', ['H2']),
              ('H1 H0 X0 CX01 X0 H1 H0', ['D12⁼']),
              ('Z0 H1 H0 CX01 H1 H0 Z0', ['H2']),
              ('Z0 CX10 Z0', ['D9⁼'])])
# Z on the target, around and past the CNOT.
D('D13t⁼', 2, [('CX10 Z0 CX10', None),
               ('Z0 Z0 CX10 Z0 CX10', ['T8']),
               ('Z0 CX10 Z1 CX10', ['D13⁼']),
               ('Z0 Z1', ['D6S⁼', 'D5⁼'])])
D('D13s⁼', 2, [('CX10 Z0', None),
               ('CX10 Z0 CX10 CX10', ['D5⁼']),
               ('Z0 Z1 CX10', ['D13t⁼'])])
# T† on the target passes the diagonal CX T† CX.
D('D8cd⁼', 2, [('Td0 CX10 Td0 CX10', None),
               ('Td0 CX01 Td1 CX01', ['D8d⁼']),
               ('CX01 Td1 CX01 Td0', ['D6t⁼']),
               ('CX10 Td0 CX10 Td0', ['D8d⁼'])])
# T on the control passes it too.
D('KT1⁼', 2, [('T0 CX10 Td0 CX10 T1', None), ('T1 T0 CX10 Td0 CX10', ['D6⁼'])])

# ---------------------------------------------------------------------
# The controlled gates: CH (control on wire 1), CHw = CH H (the control
# negated), CS, and the CNOT with a negated control CXw = CX X.  The
# paper passes a diagonal gate through them in one step labelled with
# the definitions and (D.6), (D.8); here each such passage is a lemma.

# The controlled S is diagonal: phases on either wire pass it, and its
# inverse CS† = CS³.
D('CST1⁼', 2, [('T1 CS', None), ('CS T1', ['D6⁼'])])
D('CSTd1⁼', 2, [('Td1 CS', None), ('CS Td1', ['D6t⁼'])])
D('CST0⁼', 2, [('T0 CS', None), ('CS T0', ['D8c⁼'])])
D('CSS0⁼', 2, [('S0 CS', None), ('CS S0', ['CST0⁼'])])
D('CSZ0⁼', 2, [('Z0 CS', None), ('CS Z0', ['CSS0⁼'])])
D('CSTd0⁼', 2, [('Td0 CS', None), ('CS Td0', ['CST0⁼', 'CSS0⁼', 'CSZ0⁼'])])
D('CSSd0⁼', 2, [('Sd0 CS', None), ('CS Sd0', ['CSS0⁼', 'CSZ0⁼'])])
D('CSdT0⁼', 2, [('T0 CSd', None), ('CSd T0', ['CST0⁼'])])
D('CSdS0⁼', 2, [('S0 CSd', None), ('CSd S0', ['CSdT0⁼'])])
D('CSdZ0⁼', 2, [('Z0 CSd', None), ('CSd Z0', ['CSdS0⁼'])])
D('CSdTd0⁼', 2, [('Td0 CSd', None), ('CSd Td0', ['CSdT0⁼', 'CSdS0⁼', 'CSdZ0⁼'])])
D('CSdSd0⁼', 2, [('Sd0 CSd', None), ('CSd Sd0', ['CSdS0⁼', 'CSdZ0⁼'])])

# Phases on the control pass the controlled Hadamards.
D('CHwT1⁼', 2, [('T1 CHw', None), ('CHw T1', ['D6⁼'])])
D('CHwS1⁼', 2, [('S1 CHw', None), ('CHw S1', ['CHwT1⁼'])])
D('CHwZ1⁼', 2, [('Z1 CHw', None), ('CHw Z1', ['CHwS1⁼'])])
D('CHwTd1⁼', 2, [('Td1 CHw', None), ('CHw Td1', ['CHwT1⁼', 'CHwS1⁼', 'CHwZ1⁼'])])

# D.14: H on the target passes the controlled Hadamard.
D('D14⁼', 2, [('H0 CHw', None),
              ('Sd0 H0 Sd0 T0 CX10 Td0 S0 H0 S0', ['E', 'w8']),
              ('Sd0 H0 Td0 CX10 T0 H0 S0', ['T8']),
              ('S0 Z0 H0 Td0 CX10 T0 H0 Z0 Sd0', ['T8']),
              ('S0 H0 X0 Td0 CX10 T0 X0 H0 Sd0', ['D3⁼', 'H2']),
              ('S0 H0 T0 X0 CX10 X0 Td0 H0 Sd0', ['TX', 'XT⁼', 'w8']),
              ('CH', ['D11⁼', 'D2⁼']),
              ('CHw H0', ['H2'])])
# … and so H on the target turns CH into the negated one.
D('HCH⁼', 2, [('H0 CH', None),
              ('H0 CH H0 H0', ['H2']),
              ('CH H0 H0 H0', ['D14⁼']),
              ('CHw', ['H2'])])

# D.15: the CNOT and the negated controlled Hadamard commute.
D('D15⁼', 2, [('CX10 CHw', None),
              ('H0 H0 CX10 H0 CHw H0', ['H2', 'D14⁼']),
              ('H0 S1 S0 CX10 Sd0 CX10 CHw H0', ['CZ']),
              ('H0 T1 T1 T0 T0 CX10 Td0 CX10 CX10 Td0 CX10 CHw H0', ['T8', 'D5⁼']),
              ('H0 T1 T0 T0 CX10 Td0 CX10 T1 CX10 Td0 CX10 CHw H0', ['D6⁼']),
              ('H0 CS CS CHw H0', ['D8c⁼']),
              ('H0 CHw CS CS H0', ['CSH']),
              ('CHw H0 CS CS H0', ['D14⁼']),
              ('CHw H0 T1 T0 T0 CX10 Td0 CX10 T1 CX10 Td0 CX10 H0', ['D8c⁼']),
              ('CHw H0 S1 S0 CX10 Td0 CX10 CX10 Td0 CX10 H0', ['D6⁼']),
              ('CHw H0 S1 S0 CX10 Sd0 CX10 H0', ['D5⁼', 'T8']),
              ('CHw H0 H0 CX10 H0 H0', ['CZ']),
              ('CHw CX10', ['H2'])])

# D.16: the negated controlled Hadamard through the negated CNOT.
D('D16⁼', 2, [('CHw', None),
              ('wd S0 H0 T0 CX10 Td0 S0 H0 S0', ['E']),
              ('wd S0 H0 T0 CX10 Td0 S0 X0 H0 Sd0', ['T8', 'D3⁼', 'H2']),
              ('S0 H0 T0 CX10 X0 T0 Sd0 H0 Sd0', ['TX', 'XT⁼', 'w8', 'T8', 'D11⁼']),
              ('S0 H0 T0 CXw Td0 H0 Sd0', [])])

# D.17: X on the control exchanges the two controlled Hadamards.
D('D17⁼', 2, [('X1 CHw X1', None),
              ('X1 S0 H0 T0 CXw Td0 H0 Sd0 X1', ['D16⁼']),
              ('CH', ['D12⁼', 'D2⁼'])])
D('XCH⁼', 2, [('CH X1', None), ('X1 CHw', ['D17⁼', 'D2⁼'])])
D('CHwX⁼', 2, [('CHw X1', None), ('X1 CH', ['D17⁼', 'D2⁼'])])

# D.18: the controlled Hadamard is an involution.
D('D18⁼', 2, [('CH CH', None),
              ('S0 H0 T0 CX10 CX10 Td0 H0 Sd0', ['T8', 'H2']),
              ('S0 H0 T0 Td0 H0 Sd0', ['D5⁼']),
              ('', ['T8', 'H2'])])

# D.19: the controlled S has order 4 (CS = T↑ K, K diagonal).
K = 'T0 CX10 Td0 CX10'
D('D19⁼', 2, [('CS CS CS CS', None),
              ('T1 T1 %s %s CS CS' % (K, K), ['KT1⁼']),
              ('T1 T1 T1 %s %s %s CS' % (K, K, K), ['KT1⁼']),
              ('Z1 %s %s %s %s' % (K, K, K, K), ['KT1⁼']),
              ('Z1 T0 T0 CX10 Td0 CX10 CX10 Td0 CX10 %s %s' % (K, K), ['D8c⁼']),
              ('Z1 Z0 CX10 Td0 CX10 CX10 Td0 CX10 CX10 Td0 CX10 CX10 Td0 CX10', ['D8c⁼']),
              ('Z1 Z0 CX10 Td0 Td0 Td0 Td0 CX10', ['D5⁼']),
              ('Z1 Z0 CX10 Z0 CX10', ['T8']),
              ('Z1 Z0 Z0 Z1', ['D13t⁼']),
              ('', ['T8'])])
# … so CS³ is its inverse word.
D('CSinv⁼', 2, [('Td1 Td0 CX10 T0 CX10', None),
                ('CS CS CS CS Td1 Td0 CX10 T0 CX10', ['D19⁼']),
                ('CS CS CS T1 Td1 T0 Td0 CX10 Td0 CX10 CX10 T0 CX10', ['D6t⁼', 'D8cd⁼']),
                ('CS CS CS CX10 Td0 T0 CX10', ['T8', 'D5⁼']),
                ('CSd', ['T8', 'D5⁼'])])

# D.20: the controlled S squared is CZ.
D('D20⁼', 2, [('CS CS', None),
              ('S1 T0 CX10 Td0 CX10 T0 CX10 Td0 CX10', ['D6⁼']),
              ('S1 S0 CX10 Td0 CX10 CX10 Td0 CX10', ['D8c⁼']),
              ('S1 S0 CX10 Sd0 CX10', ['D5⁼', 'T8']),
              ('H0 CX10 H0', ['CZ'])])

# D.21, D.22: S on the target against the controlled S.
D('D21⁼', 2, [('Sd0 CS', None),
              ('Td0 T1 CX01 Td1 CX01', ['T8', 'D8d⁼']),
              ('Td0 T1 X1 CX01 X1 Td1 X1 CX01 X1', ['D11⁼', 'D2⁼']),
              ('Td0 X1 Td1 CX01 T1 CX01 X1', ['TX', 'XT⁼', 'D2⁼', 'w8']),
              ('X1 T1^3 Z1 T0 Z0 CX01 T1 CX01 T0 T0 X1', ['D6⁼']),
              ('X1 T1^3 T0 CX01 T1^5 CX01 T0 T0 X1', ['D13s⁼', 'T8']),
              ('X1 T1^3 T0 CX01 Td1 Td1 Td1 T0 T0 CX01 X1', ['D6⁼', 'T8']),
              ('X1 T1^3 T0 CX01 Td1 CX01 T0 CX01 Td1 CX01 T0 CX01 Td1 CX01 X1',
               ['D5⁼', 'D6⁼']),
              ('X1 T1^3 T0 CX10 Td0 CX10 T0 CX10 Td0 CX10 T0 CX10 Td0 CX10 X1', ['D8d⁼']),
              ('X1 CSd X1', ['KT1⁼'])])
D('D22⁼', 2, [('S0 CSd', None),
              ('Sd0 Sd0 Sd0 CS CS CS', ['T8']),
              ('Sd0 CS Sd0 CS Sd0 CS', ['CSSd0⁼']),
              ('X1 CSd X1 X1 CSd X1 X1 CSd X1', ['D21⁼']),
              ('X1 CSd CSd CSd X1', ['D2⁼']),
              ('X1 CS X1', ['D19⁼'])])

# D.23: (HT²) with S T in place of T.
D('D23⁼', 2, [('CH S0 T0 CHw Td0 Sd0', None),
              ('CH S0 CSd CS T0 CHw Td0 Sd0', ['D19⁼']),
              ('CH X1 CS X1 CS T0 CHw Td0 Sd0', ['D22⁼']),
              ('X1 CHw CS X1 CS T0 CHw Td0 Sd0', ['XCH⁼']),
              ('X1 CS CHw X1 CS T0 CHw Td0 Sd0', ['CSH']),
              ('X1 CS X1 CH CS T0 CHw Td0 Sd0', ['CHwX⁼']),
              ('X1 CS X1 CH T0 CS CHw Td0 Sd0', ['CST0⁼']),
              ('X1 CS X1 CH T0 CHw CS Td0 Sd0', ['CSH']),
              ('X1 CS X1 CH T0 CHw Td0 Sd0 CS', ['CSTd0⁼', 'CSSd0⁼']),
              ('X1 CS X1 CH T0 CHw Td0 X1 CSd X1', ['D21⁼']),
              ('X1 CS X1 T0 CHw Td0 CH X1 CSd X1', ['HT2']),
              ('X1 CS T0 X1 CHw Td0 X1 CHw CSd X1', ['XCH⁼']),
              ('X1 CS T0 X1 CHw Td0 X1 CSd CHw X1', ['CSH']),
              ('X1 CS T0 X1 CHw Td0 X1 CSd X1 CH', ['CHwX⁼']),
              ('S0 CSd T0 CHw Td0 Sd0 CS CH', ['D21⁼', 'D22⁼']),
              ('S0 T0 CSd CHw CS Td0 Sd0 CH', ['CSdT0⁼', 'CSTd0⁼', 'CSSd0⁼']),
              ('S0 T0 CSd CS CHw Td0 Sd0 CH', ['CSH']),
              ('S0 T0 CHw Td0 Sd0 CH', ['D19⁼'])])

# D.31: (C18).
D('D31⁼', 2, [('CX10 T0 H0 Td0 CXw T0 H0 Td0', None),
              ('CX10 T0 H0 Td0 X0 CXw X0 T0 H0 Td0', ['D11⁼', 'D2⁼']),
              ('CX10 T0 H0 X0 T0 CXw Td0 X0 H0 Td0', ['TX', 'XT⁼', 'w8']),
              ('CX10 T0 Z0 H0 T0 CXw Td0 H0 Z0 Td0', ['D3⁼', 'H2']),
              ('CX10 T0 S0 CHw Sd0 Td0', ['D16⁼', 'T8']),
              ('CX10 Z0 Td0 CHw Sd0 Td0', ['T8']),
              ('Z1 Z0 CX10 Td0 CHw Sd0 Td0', ['D13s⁼']),
              ('Z1 Z0 CX10 Td0 CX10 CX10 CHw Sd0 Td0', ['D5⁼']),
              ('Z1 Td1 T1 Z0 Td0 T0 CX10 Td0 CX10 CX10 CHw Sd0 Td0', ['T8']),
              ('Z1 Td1 Z0 Td0 CS CX10 CHw Sd0 Td0', []),
              ('Z1 Td1 Z0 Td0 CHw CS CX10 Sd0 Td0', ['CSH', 'D15⁼']),
              ('Z0 Td0 CHw Z1 Td1 CS CX10 Sd0 Td0', ['CHwZ1⁼', 'CHwTd1⁼']),
              ('Z0 Td0 CHw Z1 T0 CX10 Td0 Sd0 Td0', ['T8', 'D5⁼']),
              ('Z0 Td0 CHw Z1 T0 CX10 Z0', ['T8']),
              ('S0 T0 CHw Sd0 Td0 CX10', ['D13s⁼', 'T8']),
              ('T0 Z0 H0 T0 CXw Td0 H0 Z0 Td0 CX10', ['D16⁼', 'T8']),
              ('T0 H0 X0 T0 CXw Td0 X0 H0 Td0 CX10', ['D3⁼', 'H2']),
              ('T0 H0 Td0 X0 CXw X0 T0 H0 Td0 CX10', ['TX', 'XT⁼', 'w8']),
              ('T0 H0 Td0 CXw T0 H0 Td0 CX10', ['D11⁼', 'D2⁼'])])

# D.32: (C19).
D('D32⁼', 2, [('CX10 T0 H0 T0 H0 Td0 CXw T0 H0 Td0 H0 Td0', None),
              ('CX10 T0 H0 T0 H0 Td0 X0 CXw X0 T0 H0 Td0 H0 Td0', ['D11⁼', 'D2⁼']),
              ('CX10 T0 H0 T0 H0 X0 T0 CXw Td0 X0 H0 Td0 H0 Td0', ['TX', 'XT⁼', 'w8']),
              ('CX10 T0 H0 T0 Z0 H0 T0 CXw Td0 H0 Z0 Td0 H0 Td0', ['D3⁼', 'H2']),
              ('CX10 T0 H0 T0 S0 CHw Sd0 Td0 H0 Td0', ['D16⁼', 'T8']),
              ('CX10 T0 H0 T0 S0 CHw Sd0 Td0 H0 CX10 CX10 Td0 CX10 CX10', ['D5⁼']),
              ('CX10 T0 H0 T0 S0 CHw Sd0 Td0 H0 CX10 T0 Td0 CX10 Td0 CX10 T1 Td1 CX10',
               ['T8']),
              ('CX10 T0 H0 T0 S0 CHw Sd0 Td0 H0 CX10 CS Td1 Td0 CX10', ['D6⁼', 'D8cd⁼']),
              ('CX10 T0 H0 T0 S0 CHw Sd0 Td0 H1 CX01 H1 H0 CS Td1 Td0 CX10', ['H2', 'D10⁼']),
              ('CX10 T0 H0 T0 S0 CHw H1 CX01 H1 Sd0 Td0 H0 CS Td1 Td0 CX10',
               ['D6d⁼', 'D6t⁼']),
              ('CX10 T0 H0 T0 S0 CHw CS CS Sd0 Td0 H0 CS Td1 Td0 CX10', ['D10⁼', 'D20⁼']),
              ('CX10 T0 H0 T0 S0 CS CS CHw Sd0 Td0 H0 CS Td1 Td0 CX10', ['CSH']),
              ('CX10 T0 H0 T0 S0 Td1 CS CS CHw Sd0 Td0 H0 CS Td0 CX10',
               ['CSTd1⁼', 'CHwTd1⁼']),
              ('CX10 T0 H0 T0 S0 Td1 H0 CX10 H0 CHw Sd0 Td0 H0 CS Td0 CX10', ['D20⁼']),
              ('CX10 Td1 T0 H0 H0 CX10 H0 T0 S0 CHw Sd0 Td0 H0 CS Td0 CX10',
               ['D10⁼', 'D6⁼', 'D6S⁼']),
              ('Td1 CX10 T0 CX10 H0 T0 S0 CHw Sd0 Td0 H0 CS Td0 CX10', ['H2', 'D6t⁼']),
              ('T0 Td1 Td0 CX10 T0 CX10 H0 T0 S0 CHw Sd0 Td0 H0 CS Td0 CX10', ['T8']),
              ('T0 CSd H0 T0 S0 CHw Sd0 Td0 H0 CS Td0 CX10', ['CSinv⁼']),
              ('T0 CSd H0 CH CH S0 T0 CHw Td0 Sd0 H0 CS Td0 CX10', ['D18⁼']),
              ('T0 CSd CHw CH S0 T0 CHw Td0 Sd0 H0 CS Td0 CX10', ['HCH⁼']),
              ('T0 CSd CHw S0 T0 CHw Td0 Sd0 CH H0 CS Td0 CX10', ['D23⁼']),
              ('T0 CHw CSd S0 T0 CHw Td0 Sd0 CH H0 CS Td0 CX10', ['CSH']),
              ('T0 CHw S0 T0 CSd CHw Td0 Sd0 CH H0 CS Td0 CX10', ['CSdT0⁼', 'CSdS0⁼']),
              ('T0 CHw S0 T0 CHw CSd Td0 Sd0 CH H0 CS Td0 CX10', ['CSH']),
              ('T0 CHw S0 T0 CHw Td0 Sd0 CSd CH H0 CS Td0 CX10', ['CSdTd0⁼', 'CSdSd0⁼']),
              ('T0 CHw S0 T0 CHw Td0 Sd0 CSd CHw CS Td0 CX10', []),
              ('T0 CHw S0 T0 CHw Td0 Sd0 CHw CSd CS Td0 CX10', ['CSH']),
              ('T0 CHw S0 T0 CHw Td0 Sd0 CHw Td0 CX10', ['D19⁼']),
              ('T0 H0 CH S0 T0 CHw Td0 Sd0 CH H0 Td0 CX10', ['HCH⁼']),
              ('T0 H0 CH CH S0 T0 CHw Td0 Sd0 H0 Td0 CX10', ['D23⁼']),
              ('T0 H0 S0 T0 CHw Td0 Sd0 H0 Td0 CX10', ['D18⁼']),
              ('T0 H0 Z0 T0 H0 T0 CXw Td0 H0 Td0 Z0 H0 Td0 CX10', ['D16⁼', 'T8']),
              ('T0 H0 T0 H0 X0 T0 CXw Td0 X0 H0 Td0 H0 Td0 CX10', ['D3⁼', 'H2']),
              ('T0 H0 T0 H0 Td0 X0 CXw X0 T0 H0 Td0 H0 Td0 CX10', ['TX', 'XT⁼', 'w8']),
              ('T0 H0 T0 H0 Td0 CXw T0 H0 Td0 H0 Td0 CX10', ['D11⁼', 'D2⁼'])])

