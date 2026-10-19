"""RCliff₂: the axioms as letter-list equations, for the derivation
machinery of frag.py.  Z is a gate of its own here (circ.PRIMITIVE), X
is H Z H, and m is the scalar −1.  Each axiom is spelled exactly as
Real-Clifford.Kit lists it."""
import circ
circ.PRIMITIVE.add('Z')
import frag
from frag import (LIB, OUT, MIRROR, NATS, LABEL, CORE, SWAPS2, SWAPS3, NATLABELS,
                  MODULES, axiom, derive, add_mirror, placed, nat, outer, outer2, emit)

axiom('−²⁼', 0, 'm m', '')
axiom('H²⁼', 1, 'H0 H0', '')
axiom('Z²⁼', 1, 'Z0 Z0', '')
axiom('F⁼', 1, 'Z0 H0 Z0 H0', 'm H0 Z0 H0 Z0')
axiom('CX²⁼', 2, 'CX10 CX10', '')
axiom('B⁼', 2, 'CX10 CX01', 'SW01 CX10')
axiom('ZC⁼', 2, 'Z0 CX10 Z0', 'CX10 Z1')
axiom('CZr⁼', 2, 'H1 H0 CX10 H1 H0', 'CX01')
axiom('CF⁼', 2, 'CX10 H0 CX10 Z0 H0', 'H0 Z0 CX10 H0 CX10')
axiom('I⁼', 3, 'CX10 CX21 CX20', 'CX21 CX10')
axiom('σσ⁼', 2, 'SW01 SW01', '')
axiom('σH⁼', 2, 'H0 SW01', 'SW01 H1')
axiom('σZ⁼', 2, 'Z0 SW01', 'SW01 Z1')
axiom('σCX⁼', 3, 'CX10 SW12 SW01', 'SW12 SW01 CX21')
axiom('σσσ⁼', 3, 'SW01 SW12 SW01', 'SW12 SW01 SW12')

LABEL.update({'m2': '−²⁼', 'H2': 'H²⁼', 'Z2': 'Z²⁼', 'F': 'F⁼', 'CX2': 'CX²⁼', 'B': 'B⁼',
              'ZC': 'ZC⁼', 'CZr': 'CZr⁼', 'CF': 'CF⁼', 'I': 'I⁼', 'ss': 'σσ⁼',
              'sH': 'σH⁼', 'sZ': 'σZ⁼', 'sCX': 'σCX⁼', 'sss': 'σσσ⁼'})

CORE += ['H²⁼', 'Z²⁼', '−²⁼', 'σσ⁼', 'CX²⁼']
SWAPS2 += ['σH⁼', 'σZ⁼']
SWAPS3 += ['σCX⁼', 'σσσ⁼']
NATLABELS += ['sH', 'sZ', 'ss', 'sCX', 'sss', 'σH′⁼', 'σZ′⁼']

frag.SELFINV.update({'H', 'Z', 'CX', 'SW', 'm'})

MODULES.update({'syntax': 'Examples.Independence.Real-Clifford.Syntactics',
                'kit': 'Examples.Independence.Real-Clifford.Kit',
                'kitname': 'Real-Clifford.Kit'})
