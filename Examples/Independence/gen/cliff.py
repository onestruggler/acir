"""Cliff₂: the axioms as letter-list equations, for the derivation
machinery of frag.py.

Every equation keeps its two sides as abstract gates (ga, gb) as well as
letters, so that it can be moved to other wires by conjugating with a
swap: the swap passes each spelled gate by a naturality lemma (nat),
and the moved equation comes out in canonical spelling."""
import frag
from frag import (LIB, OUT, MIRROR, NATS, LABEL, CORE, SWAPS2, SWAPS3, NATLABELS,
                  MODULES, axiom, derive, add_mirror, placed, nat, outer, outer2, emit)

axiom('ω⁸⁼', 0, 'w8', '')
axiom('H²⁼', 1, 'H0 H0', '')
axiom('S⁴⁼', 1, 'S0 S0 S0 S0', '')
axiom('E⁼', 1, 'H0 S0 H0', 'w Sd0 H0 Sd0')
axiom('CPh⁼', 2, 'CX10 S1 CX10', 'S1')
axiom('B⁼', 2, 'CX10 CX01', 'SW01 CX10')
axiom('CZ⁼', 2, 'H0 CX10 H0', 'S1 S0 CX10 Sd0 CX10')
axiom('I⁼', 3, 'CX10 CX21 CX20', 'CX21 CX10')
axiom('σσ⁼', 2, 'SW01 SW01', '')
axiom('σH⁼', 2, 'H0 SW01', 'SW01 H1')
axiom('σS⁼', 2, 'S0 SW01', 'SW01 S1')
axiom('σCX⁼', 3, 'CX10 SW12 SW01', 'SW12 SW01 CX21')
axiom('σσσ⁼', 3, 'SW01 SW12 SW01', 'SW12 SW01 SW12')

LABEL.update({'H2': 'H²⁼', 'S4': 'S⁴⁼', 'E': 'E⁼', 'CPh': 'CPh⁼', 'B': 'B⁼', 'CZ': 'CZ⁼',
              'I': 'I⁼', 'w8': 'ω⁸⁼', 'ss': 'σσ⁼', 'sH': 'σH⁼', 'sS': 'σS⁼', 'sCX': 'σCX⁼',
              'sss': 'σσσ⁼'})

CORE += ['H²⁼', 'S⁴⁼', 'ω⁸⁼', 'σσ⁼']
SWAPS2 += ['σH⁼', 'σS⁼']
SWAPS3 += ['σCX⁼', 'σσσ⁼']
NATLABELS += ['sH', 'sS', 'ss', 'sCX', 'sss', 'σH′⁼', 'σS′⁼']

MODULES.update({'syntax': 'Examples.Independence.Clifford.Syntactics',
                'kit': 'Examples.Independence.Clifford.Kit',
                'kitname': 'Clifford.Kit'})
