"""CliffT₂: its axioms and symmetry rules as letter-list equations.

T is the only phase gate: S, S†, Z, X and T† are spelled over it
(circ.T_SPELL), as Examples.Independence.Clifford+T.Syntactics defines
them.  The shortcuts of Figure 9 are strings: CH, the controlled
Hadamard with its control on wire 1, CH0 = CH H (the control negated),
CS, and the same with the wires exchanged by the swap."""
import circ
circ.T_SPELL = True
from frag import *
import frag as _frag

CH = 'S0 H0 T0 CX10 Td0 H0 Sd0'
CH0 = CH + ' H0'
CS = 'T1 T0 CX10 Td0 CX10'
CHd = 'SW01 ' + CH + ' SW01'
CH0d = 'SW01 ' + CH0 + ' SW01'

axiom('ω⁸⁼', 0, 'w8', '')
axiom('T⁸⁼', 1, 'T0^8', '')
axiom('H²⁼', 1, 'H0 H0', '')
axiom('E⁼', 1, 'H0 S0 H0', 'w Sd0 H0 Sd0')
axiom('TX⁼', 1, 'w Td0 X0', 'X0 T0')
axiom('CPh⁼', 2, 'CX10 T1 CX10', 'T1')
axiom('B⁼', 2, 'CX10 CX01', 'SW01 CX10')
axiom('CZ⁼', 2, 'H0 CX10 H0', 'S1 S0 CX10 Sd0 CX10')
axiom('CSH⁼', 2, CS + ' ' + CH0, CH0 + ' ' + CS)
axiom('HT²⁼', 2, CH + ' T0 ' + CH0 + ' Td0', 'T0 ' + CH0 + ' Td0 ' + CH)
axiom('HTH⁼', 2, CH0 + ' T0 ' + CH + ' ' + CH0d + ' T1 ' + CHd,
      CH0d + ' T1 ' + CHd + ' ' + CH0 + ' T0 ' + CH)
axiom('σσ⁼', 2, 'SW01 SW01', '')
axiom('σH⁼', 2, 'H0 SW01', 'SW01 H1')
axiom('σT⁼', 2, 'T0 SW01', 'SW01 T1')
axiom('σCX⁼', 3, 'CX10 SW12 SW01', 'SW12 SW01 CX21')
axiom('σσσ⁼', 3, 'SW01 SW12 SW01', 'SW12 SW01 SW12')

# The controlled gates of the paper's figures, as tokens: CH the
# controlled Hadamard with its control on wire 1 (CHw with the control
# negated), CS the controlled S, CXw the CNOT with its control negated;
# the suffix d puts the control on wire 0 (the gate under the swap),
# and CSf is CS spelt from wire 0.
circ.MACROS.update({
    'CH': CH, 'CHw': CH0, 'CHd': CHd, 'CHwd': CH0d,
    'CS': CS, 'CSd': CS + ' ' + CS + ' ' + CS, 'CSf': 'T0 T1 CX01 Td1 CX01',
    'CXw': 'CX10 X0', 'CXwd': 'CX01 X1'})

for _e in list(LIB.values()):
    assert circ.same(_e.lhs, _e.rhs, max(_e.arity, 1)), _e.name

LABEL.update({'w8': 'ω⁸⁼', 'T8': 'T⁸⁼', 'H2': 'H²⁼', 'E': 'E⁼', 'TX': 'TX⁼', 'CPh': 'CPh⁼',
              'B': 'B⁼', 'CZ': 'CZ⁼', 'CSH': 'CSH⁼', 'HT2': 'HT²⁼', 'HTH': 'HTH⁼',
              'ss': 'σσ⁼', 'sH': 'σH⁼', 'sT': 'σT⁼', 'sCX': 'σCX⁼', 'sss': 'σσσ⁼'})
CORE[:] = ['H²⁼', 'T⁸⁼', 'ω⁸⁼', 'σσ⁼']
SWAPS2[:] = ['σH⁼', 'σT⁼']
SWAPS3[:] = ['σCX⁼', 'σσσ⁼']
NAT2[:] = ['σH⁼', 'σT⁼', 'σσ⁼', 'σH′⁼', 'σT′⁼']
NAT3[:] = ['σCX⁼', 'σσσ⁼']

_frag.SYN = 'Examples.Independence.Clifford+T.Syntactics'
_frag.KIT = 'Examples.Independence.Clifford+T.Kit'
