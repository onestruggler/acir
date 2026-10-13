"""RCliff₂: its axioms and symmetry rules as letter-list equations."""
import circ
circ.PRIMITIVE_Z = True
from frag import *
import frag as _frag

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
              'ZC': 'ZC⁼', 'CZr': 'CZr⁼', 'CF': 'CF⁼', 'I': 'I⁼', 'ss': 'σσ⁼', 'sH': 'σH⁼',
              'sZ': 'σZ⁼', 'sCX': 'σCX⁼', 'sss': 'σσσ⁼'})
CORE[:] = ['H²⁼', 'Z²⁼', '−²⁼', 'CX²⁼', 'σσ⁼']
SWAPS2[:] = ['σH⁼', 'σZ⁼']
SWAPS3[:] = ['σCX⁼', 'σσσ⁼']
NAT2[:] = ['σH⁼', 'σZ⁼', 'σσ⁼', 'σH′⁼', 'σZ′⁼']
NAT3[:] = ['σCX⁼', 'σσσ⁼']

_frag.SYN = 'Examples.Independence.Real-Clifford.Syntactics'
_frag.KIT = 'Examples.Independence.Real-Clifford.Kit'
