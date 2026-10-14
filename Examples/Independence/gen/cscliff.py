"""CliffCS₂: the axioms as letter-list equations, for the derivation
machinery of frag.py.  The gates are ω, H, S and CS (a letter of its
own, symmetric in its wires); CX is H CS CS H on its target and X is
H S S H, as Syntactics defines them, and the paper's figures draw CS
with two dots, which figparse reads as CZ.  Each axiom is spelled
exactly as Clifford+CS.Kit lists it."""
import re
import circ
import frag
from frag import (LIB, OUT, MIRROR, NATS, LABEL, CORE, SWAPS2, SWAPS3, NATLABELS,
                  MODULES, axiom, derive, add_mirror, placed, nat, outer, outer2, emit)


def H(k): return [('H', k)]
def CS(a, b): return [('CS', min(a, b), max(a, b))]


def CX(c, t): return H(t) + CS(c, t) + CS(c, t) + H(t)


def mac(rx, fn):
    circ.MACROS.append((re.compile(rx), fn))


mac(r'CS(\d)(\d)', lambda m: CS(int(m[1]), int(m[2])))
mac(r'CZ(\d)(\d)', lambda m: CS(int(m[1]), int(m[2])))
mac(r'CX(\d)(\d)', lambda m: CX(int(m[1]), int(m[2])))

axiom('ω⁸⁼', 0, 'w8', '')
axiom('H²⁼', 1, 'H0 H0', '')
axiom('S⁴⁼', 1, 'S0 S0 S0 S0', '')
axiom('E⁼', 1, 'H0 S0 H0', 'w Sd0 H0 Sd0')
axiom('CPh⁼', 2, 'CS10 S1 CS10 CS10 CS10', 'S1')
axiom('CSr⁼', 2, 'CS10', 'SW01 CS10 SW01')
axiom('B⁼', 2, 'CX10 SW01 CX10 SW01', 'SW01 CX10')
axiom('XCS⁼', 2, 'X1 CS10', 'CS10 CS10 CS10 X1 S0')
axiom('CE⁼', 2, 'S1 H1 CS10 H1 CS10', 'CS10 H1 CS10 H1 S1')
axiom('I⁼', 3, 'CX10 CX21 SW01 CX21 SW01', 'CX21 CX10')
for k in range(4):
    axiom('SH%s⁼' % '₀₁₂₃'[k], 3,
          ' '.join(['CS10', 'H1'] + ['CS10'] * k + ['H1', 'CS21', 'H1'] + ['CS21'] * k),
          ' '.join(['CS21', 'H1'] + ['CS21'] * k + ['H1', 'CS10', 'H1'] + ['CS10'] * k))
axiom('σσ⁼', 2, 'SW01 SW01', '')
axiom('σH⁼', 2, 'H0 SW01', 'SW01 H1')
axiom('σS⁼', 2, 'S0 SW01', 'SW01 S1')
axiom('σCS⁼', 3, 'CS10 SW12 SW01', 'SW12 SW01 CS21')
axiom('σσσ⁼', 3, 'SW01 SW12 SW01', 'SW12 SW01 SW12')

LABEL.update({'w8': 'ω⁸⁼', 'H2': 'H²⁼', 'S4': 'S⁴⁼', 'E': 'E⁼', 'Ct': 'CPh⁼', 'CSr': 'CSr⁼',
              'B': 'B⁼', 'XCS': 'XCS⁼', 'CE': 'CE⁼', 'I': 'I⁼',
              'ss': 'σσ⁼', 'sH': 'σH⁼', 'sS': 'σS⁼', 'sCS': 'σCS⁼', 'sss': 'σσσ⁼'})

CORE += ['H²⁼', 'S⁴⁼', 'ω⁸⁼', 'σσ⁼']
SWAPS2 += ['σH⁼', 'σS⁼']
SWAPS3 += ['σCS⁼', 'σσσ⁼']
NATLABELS += ['sH', 'sS', 'ss', 'sCS', 'sss', 'CSr']

frag.SELFINV.update({'H', 'SW'})

MODULES.update({'syntax': 'Examples.Independence.Clifford+CS.Syntactics',
                'kit': 'Examples.Independence.Clifford+CS.Kit',
                'kitname': 'Clifford+CS.Kit'})
