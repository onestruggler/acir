"""CliffT₂: the axioms as letter-list equations, for the derivation
machinery of frag.py.  T is the gate; S is T T, S† T⁶, Z T⁴, X H Z H and
T† T⁷ (Figure 9), and the controlled gates are spelled as Syntactics
defines them: CH (control c, target t) S H T CNOT T† H S† on the
target, CHo (a negative control) CH then H, CXo CNOT then X on the
target, CS T T CNOT T† CNOT.  Each axiom is spelled exactly as
Clifford+T.Kit lists it."""
import re
import circ
import frag
from frag import (LIB, OUT, MIRROR, NATS, LABEL, CORE, SWAPS2, SWAPS3, NATLABELS,
                  MODULES, axiom, derive, add_mirror, placed, nat, outer, outer2, emit)


def T(k, m=1): return [('T', k)] * m
def H(k): return [('H', k)]
def CX(c, t): return [('CX', c, t)]


def X(k): return H(k) + T(k, 4) + H(k)


def CH(c, t): return T(t, 2) + H(t) + T(t) + CX(c, t) + T(t, 7) + H(t) + T(t, 6)


def mac(rx, fn):
    circ.MACROS.append((re.compile(rx), fn))


mac(r'S(\d)', lambda m: T(int(m[1]), 2))
mac(r'Sd(\d)', lambda m: T(int(m[1]), 6))
mac(r'Z(\d)', lambda m: T(int(m[1]), 4))
mac(r'Td(\d)', lambda m: T(int(m[1]), 7))
mac(r'X(\d)', lambda m: X(int(m[1])))
mac(r'CXo(\d)(\d)', lambda m: CX(int(m[1]), int(m[2])) + X(int(m[2])))
mac(r'CH(\d)(\d)', lambda m: CH(int(m[1]), int(m[2])))
mac(r'CHo(\d)(\d)', lambda m: CH(int(m[1]), int(m[2])) + H(int(m[2])))
mac(r'CSd(\d)(\d)', lambda m: (T(int(m[1])) + T(int(m[2])) + CX(int(m[1]), int(m[2])) +
                                  T(int(m[2]), 7) + CX(int(m[1]), int(m[2]))) * 3)
mac(r'CS(\d)(\d)', lambda m: T(int(m[1])) + T(int(m[2])) + CX(int(m[1]), int(m[2])) +
    T(int(m[2]), 7) + CX(int(m[1]), int(m[2])))

axiom('ω⁸⁼', 0, 'w8', '')
axiom('T⁸⁼', 1, 'T0 T0 T0 T0 T0 T0 T0 T0', '')
axiom('H²⁼', 1, 'H0 H0', '')
axiom('E⁼', 1, 'H0 S0 H0', 'w Sd0 H0 Sd0')
axiom('TX⁼', 1, 'w Td0 X0', 'X0 T0')
axiom('CPh⁼', 2, 'CX10 T1 CX10', 'T1')
axiom('B⁼', 2, 'CX10 CX01', 'SW01 CX10')
axiom('CZ⁼', 2, 'H0 CX10 H0', 'S1 S0 CX10 Sd0 CX10')
axiom('CSH⁼', 2, 'CS10 CHo10', 'CHo10 CS10')
axiom('HT²⁼', 2, 'CH10 T0 CHo10 Td0', 'T0 CHo10 Td0 CH10')
axiom('HTH⁼', 2, 'CHo10 T0 CH10 SW01 CHo10 SW01 T1 SW01 CH10 SW01',
      'SW01 CHo10 SW01 T1 SW01 CH10 SW01 CHo10 T0 CH10')
axiom('σσ⁼', 2, 'SW01 SW01', '')
axiom('σH⁼', 2, 'H0 SW01', 'SW01 H1')
axiom('σT⁼', 2, 'T0 SW01', 'SW01 T1')
axiom('σCX⁼', 3, 'CX10 SW12 SW01', 'SW12 SW01 CX21')
axiom('σσσ⁼', 3, 'SW01 SW12 SW01', 'SW12 SW01 SW12')

LABEL.update({'w8': 'ω⁸⁼', 'T8': 'T⁸⁼', 'S4': 'T⁸⁼', 'H2': 'H²⁼', 'E': 'E⁼', 'TX': 'TX⁼',
              'Ct': 'CPh⁼', 'B': 'B⁼', 'CZ': 'CZ⁼', 'CsCh': 'CSH⁼', 'HTHT': 'HT²⁼',
              'HTH': 'HTH⁼', 'ss': 'σσ⁼', 'sH': 'σH⁼', 'sT': 'σT⁼', 'sCX': 'σCX⁼',
              'sss': 'σσσ⁼'})

CORE += ['H²⁼', 'T⁸⁼', 'ω⁸⁼', 'σσ⁼']
SWAPS2 += ['σH⁼', 'σT⁼']
SWAPS3 += ['σCX⁼', 'σσσ⁼']
NATLABELS += ['sH', 'sT', 'ss', 'sCX', 'sss', 'σH′⁼', 'σT′⁼']

frag.SELFINV.update({'H', 'CX', 'SW'})

MODULES.update({'syntax': 'Examples.Independence.Clifford+T.Syntactics',
                'kit': 'Examples.Independence.Clifford+T.Kit',
                'kitname': 'Clifford+T.Kit'})
