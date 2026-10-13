"""Cliff₂'s axioms, read in CliffCS₂ (CX as H CS CS H), derived there.

Only (CPh), (CZ) and the swap rule for CX need work: (ω⁸), (H²), (S⁴),
(E), (B) and (I) are CliffCS₂'s own, letter for letter.  (CZ) comes
down to the CNOT conjugating S on its target (CXS1, from CXCS of
twoq.py), mirrored."""
import twoq
from twoq import T, C3
from appendixE import LIB, OUT, add_mirror

first = len(OUT)

# The CNOT from wire 0 conjugates S1 to S0 S1 CZ.
T('CXS1⁼', 2, [('CX01 S1 CX01', None),
               ('CX01 CS01 S1 ' + C3 + ' CX01', ['E3⁼', 'E2⁼']),
               ('CX01 CS01 CX01 CX01 S1 ' + C3 + ' CX01', ['CXCX↓⁼']),
               (C3 + ' S0 CX01 S1 ' + C3 + ' CX01', ['CXCS⁼']),
               (C3 + ' S0 S1 ' + C3 + ' CX01 CX01', ['A2B⁼']),
               (C3 + ' S0 S1 ' + C3, ['CXCX↓⁼']),
               ('S0 S1 CS01 CS01', ['E3⁼', 'E4⁼', 'E2⁼'])])
CXS1M = add_mirror('CXS1⁼')                     # CX10 S0 CX10 = S1 S0 CZ

# (CPh): S on the control passes the CNOT.
T('TCPh⁼', 2, [('CX10 S1 CX10', None), ('S1 CX10 CX10', ['E3⁼']), ('S1', ['CXCX⁼'])])

# (CZ), read backwards: S1 S0 CX S0³ CX is CZ, which is H CX H.
T('SScc⁼', 2, [('S1 S0 CS01 CS01', None), ('CS01 CS01 S1 S0', ['E3⁼', 'E4⁼'])])
T('TCZ′⁼', 2, [('S1 S0 CX10 S0 S0 S0 CX10', None),
               ('S1 S0 CX10 S0 CX10 CX10 S0 CX10 CX10 S0 CX10', ['CXCX⁼']),
               ('S1 S0 S1 S0 CS01 CS01 S1 S0 CS01 CS01 S1 S0 CS01 CS01', [CXS1M.name]),
               ('S1 S0 S1 S0 S1 S0 S1 S0 CS01 CS01 CS01 CS01 CS01 CS01', ['SScc⁼']),
               ('CS01 CS01', ['S4', 'E2⁼']),
               ('H0 CX10 H0', ['H2'])])

# The swap rule for CX: CX passes the cycle of the three wires.
T('TσCX⁼', 3, [('CX10 SW12 SW01', None), ('SW12 SW01 CX21', ['sCS', 'sH', 'σH′⁼', 'sss'])])

del OUT[:first]
