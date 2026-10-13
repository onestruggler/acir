"""CliffCS₂: its axioms and symmetry rules as letter-list equations.

CS is a gate of its own and CNOT is the shortcut H CS CS H on its target
(circ.CS_MODE), as Examples.Independence.Clifford+CS.Syntactics defines
it; a CX token is so spelt."""
import circ
circ.CS_MODE = True
from frag import *
import frag as _frag


def SHl(k):
    return ' '.join(['CS01', 'H1'] + ['CS01'] * k + ['H1', 'CS12', 'H1'] + ['CS12'] * k)


def SHr(k):
    return ' '.join(['CS12', 'H1'] + ['CS12'] * k + ['H1', 'CS01', 'H1'] + ['CS01'] * k)


axiom('ω⁸⁼', 0, 'w8', '')
axiom('H²⁼', 1, 'H0 H0', '')
axiom('S⁴⁼', 1, 'S0 S0 S0 S0', '')
axiom('E⁼', 1, 'H0 S0 H0', 'w Sd0 H0 Sd0')
axiom('CPh⁼', 2, 'CS01 S1 CS01 CS01 CS01', 'S1')
axiom('CSr⁼', 2, 'CS01', 'SW01 CS01 SW01')
axiom('B⁼', 2, 'CX10 SW01 CX10 SW01', 'SW01 CX10')
axiom('XCS⁼', 2, 'X1 CS01', 'CS01 CS01 CS01 X1 S0')
axiom('CE⁼', 2, 'S1 H1 CS01 H1 CS01', 'CS01 H1 CS01 H1 S1')
axiom('I⁼', 3, 'CX10 CX21 SW01 CX21 SW01', 'CX21 CX10')
for _k in range(4):
    axiom('SH%s⁼' % '₀₁₂₃'[_k], 3, SHl(_k), SHr(_k))
axiom('σσ⁼', 2, 'SW01 SW01', '')
axiom('σH⁼', 2, 'H0 SW01', 'SW01 H1')
axiom('σS⁼', 2, 'S0 SW01', 'SW01 S1')
axiom('σCS⁼', 3, 'CS01 SW12 SW01', 'SW12 SW01 CS12')
axiom('σσσ⁼', 3, 'SW01 SW12 SW01', 'SW12 SW01 SW12')

for _e in list(LIB.values()):
    assert circ.same(_e.lhs, _e.rhs, max(_e.arity, 1)), _e.name

LABEL.update({'w8': 'ω⁸⁼', 'H2': 'H²⁼', 'S4': 'S⁴⁼', 'E': 'E⁼', 'CPh': 'CPh⁼', 'CSr': 'CSr⁼',
              'B': 'B⁼', 'XCS': 'XCS⁼', 'CE': 'CE⁼', 'I': 'I⁼',
              'SH0': 'SH₀⁼', 'SH1': 'SH₁⁼', 'SH2': 'SH₂⁼', 'SH3': 'SH₃⁼',
              'ss': 'σσ⁼', 'sH': 'σH⁼', 'sS': 'σS⁼', 'sCS': 'σCS⁼', 'sss': 'σσσ⁼'})
CORE[:] = ['H²⁼', 'S⁴⁼', 'ω⁸⁼', 'σσ⁼']
SWAPS2[:] = ['σH⁼', 'σS⁼']
SWAPS3[:] = ['σCS⁼', 'σσσ⁼']
NAT2[:] = ['σH⁼', 'σS⁼', 'σσ⁼', 'σH′⁼', 'σS′⁼', 'σCS′⁼']
NAT3[:] = ['σCS⁼', 'σσσ⁼']

_frag.SYN = 'Examples.Independence.Clifford+CS.Syntactics'
_frag.KIT = 'Examples.Independence.Clifford+CS.Kit'
