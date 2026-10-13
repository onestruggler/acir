"""The permutation gates on two wires (X0, X1, the swap, the two CNOTs)
and how they pass one another and the canonical gates: the calculus the
frames of cs2.py need."""
import w2canon
from twoq import T, C3, B
from appendixE import OUT, add_mirror, LIB
from cs2 import CK01

first = len(OUT)
T('νX0⁼', 2, [('X0 SW01', None), ('SW01 X1', ['sH', 'sS', 'σH′⁼', 'σS′⁼'])])
T('νX1⁼', 2, [('X1 SW01', None), ('SW01 X0', ['sH', 'sS', 'σH′⁼', 'σS′⁼'])])
T('νCX′⁼', 2, [('CX01 SW01', None), ('SW01 CX10', ['DX⁼', 'ss'])])
T('XtCX↓⁼', 2, [('X0 CX10', None), ('H0 S0 S0 CS01 CS01 H0', ['H2']),
                ('H0 CS01 CS01 S0 S0 H0', ['E4⁼']), ('CX10 X0', ['H2'])])
T('XcCX↓⁼', 2, [('X1 CX10 X1', None),
                ('H0 X1 CS01 X1 X1 CS01 X1 H0', ['XX⁼']),
                ('H0 ' + C3 + ' S0 ' + C3 + ' S0 H0', ['XD1⁼']),
                ('H0 CS01 CS01 S0 S0 H0', ['E4⁼', 'E2⁼']),
                ('CX10 X0', ['H2'])])
T('CX3⁼', 2, [('CX10 CX01 CX10', None), ('SW01 CX10 CX10', ['B′⁼']), ('SW01', ['CXCX⁼'])])
T('CX3′⁼', 2, [('CX01 CX10 CX01', None), ('SW01 CX01 CX01', ['B↓⁼']), ('SW01', ['CXCX↓⁼'])])
# (0 1) = X0 CX01 X0 passes the canonical gates.
N = 'X0 CX01 X0'
T('Nc⁼', 2, [(N + ' CS01', None), ('CX01 X1 CS01', ['XcCX⁼']),
             ('CX01 X1 CS01 X1 X1', ['XX⁼']), ('CX01 ' + C3 + ' S0 X1', ['XD1⁼']),
             ('CX01 CX01 CS01 CX01 X1', ['CXCS⁼', 'CXCX↓⁼']), ('CS01 CX01 X1', ['CXCX↓⁼']),
             ('CS01 ' + N, ['XcCX⁼'])], maxstates=40000)
del OUT[:first]
