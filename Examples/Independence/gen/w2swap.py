"""The exchange relations and (19) at their canonical indices, and the
transports of single generators that the search does not find alone."""
import w2cross
from twoq import T, dnorm, deq, C3, Q, B, TB, B3
from appendixE import OUT
from cs2 import CK01, FRAME, IFRAME, conj, DI, DX, DK

first = len(OUT)
N = 'X0 CX01 X0'
X12, X13, X02, X03 = DX[(1, 2)], DX[(1, 3)], DX[(0, 2)], DX[(0, 3)]
K12, K13, K02, K03 = DK[(1, 2)], DK[(1, 3)], DK[(0, 2)], DK[(0, 3)]
K01 = DK[(0, 1)]

# The exchanges, simplified.
T('X12s⁼', 2, [(X12, None), ('CX01 CX10 CX01', ['DX⁼']), ('SW01', ['CX3′⁼'])])
T('X13s⁼', 2, [(X13, None), ('CX10', ['DX⁼'])])
T('X02s⁼', 2, [(X02, None), ('X1 CX10 X1', ['DX⁼']), ('CX10 X0', ['XcCX↓⁼'])])
T('X03s⁼', 2, [(X03, None), ('X1 CX01 CX10 CX01 X1', ['DX⁼']), ('X1 SW01 X1', ['CX3′⁼']),
               ('SW01 X0 X1', ['νX1⁼'])])
# The two frames of (0, 3) differ by (0 1), which passes CK01.
T('Wn⁼', 2, [('X0 CX10 X1 CX01 SW01', None), ('X0 CX10 CX01 X1 SW01', ['XtCX⁼']),
             ('X0 CX10 CX01 SW01 X0', ['νX1⁼']), ('X0 SW01 CX10 SW01 X0', ['B′⁼']),
             (N, ['DX⁼'])])
T('Wn′⁼', 2, [('SW01 CX01 X1 CX10 X0', None), ('SW01 X1 CX01 CX10 X0', ['XtCX⁼']),
              ('X0 SW01 CX01 CX10 X0', ['νX1⁼']), ('X0 SW01 SW01 CX01 X0', ['B↓⁼']),
              (N, ['σσ⁼'])])
T('NN⁼', 2, [(N + ' ' + N, None), ('X0 CX01 CX01 X0', ['XX⁼']), ('', ['CXCX↓⁼', 'XX⁼'])])
T('FE03⁼', 2, [(K03, None),
               ('CX10 X0 X0 CX10 ' + K03, ['XX⁼', 'CXCX⁼']),
               ('CX10 X0 ' + N + ' ' + CK01 + ' SW01 CX01 X1', ['Wn⁼']),
               ('CX10 X0 ' + CK01 + ' ' + N + ' SW01 CX01 X1', ['CXK⁼']),
               ('CX10 X0 ' + CK01 + ' ' + N + ' SW01 CX01 X1 CX10 X0 X0 CX10', ['XX⁼', 'CXCX⁼']),
               ('CX10 X0 ' + CK01 + ' ' + N + ' ' + N + ' X0 CX10', ['Wn′⁼']),
               ('CX10 X0 ' + CK01 + ' X0 CX10', ['NN⁼'])], maxstates=40000)

# Exchange relations at (j, 2, 3), j = 1, 0.
T('SXXa⁼', 2, [('CX01 ' + X12, None), ('CX01 SW01', ['X12s⁼']), ('SW01 CX10', ['νCX′⁼']),
               (X12 + ' ' + X13, ['X12s⁼', 'X13s⁼'])])
T('SXXb⁼', 2, [('CX01 ' + X02, None), ('CX01 CX10 X0', ['X02s⁼']), ('SW01 CX01 X0', ['B↓⁼']),
               ('CX10 SW01 X0', ['νCX⁼']), ('CX10 X0 SW01 X0 X1', ['νX0⁼', 'XX⁼']),
               (X02 + ' ' + X03, ['X02s⁼', 'X03s⁼'])])
T('SXXa′⁼', 2, [(X13 + ' CX01', None), ('CX10 CX01', ['X13s⁼']), ('SW01 CX10', ['B′⁼']),
                ('CX01 SW01', ['νCX′⁼']), ('CX01 ' + X12, ['X12s⁼'])])
T('SXXb′⁼', 2, [(X03 + ' CX01', None), ('SW01 X0 X1 CX01', ['X03s⁼']),
                ('SW01 X0 CX01 X1', ['XtCX⁼']), ('SW01 CX01 X0', ['XcCX⁼', 'XX⁼']),
                ('CX01 CX10 X0', ['B↓⁼']), ('CX01 ' + X02, ['X02s⁼'])])
T('SKXa⁼', 2, [(CK01 + ' ' + X12, None), (CK01 + ' SW01', ['X12s⁼']),
               ('SW01 SW01 ' + CK01 + ' SW01', ['σσ⁼']), (X12 + ' ' + K13, ['X12s⁼'])])
T('X02sq⁼', 2, [('CX10 X0 CX10 X0', None), ('CX10 CX10 X0 X0', ['XtCX↓⁼']), ('', ['CXCX⁼', 'XX⁼'])])
T('SKXb⁼', 2, [(CK01 + ' ' + X02, None), (CK01 + ' CX10 X0', ['X02s⁼']),
               ('CX10 X0 CX10 X0 ' + CK01 + ' CX10 X0', ['X02sq⁼']),
               ('CX10 X0 CX10 X0 ' + CK01 + ' X0 CX10', ['XtCX↓⁼']),
               ('CX10 X0 ' + K03, ['FE03⁼']),
               (X02 + ' ' + K03, ['X02s⁼'])], maxstates=40000)
T('SKXa′⁼', 2, [(K13 + ' CX01', None), ('CX01 CX01 ' + K13 + ' CX01', ['CXCX↓⁼']),
                ('CX01 ' + K12, ['X13s⁼', 'DX⁼'])])
T('SKXb′⁼', 2, [(K03 + ' CX01', None),
                ('X1 CX01 SW01 ' + CK01 + ' SW01 CX01 CX01 X1', ['XtCX⁼']),
                ('X1 CX01 SW01 ' + CK01 + ' SW01 X1', ['CXCX↓⁼']),
                ('CX01 ' + K02, ['XtCX⁼'])])

# (19).
T('KK0⁼', 2, [(K02 + ' ' + K13, None),
              ('SW01 ' + K01 + ' ' + CK01 + ' SW01', ['νX1⁼', 'σσ⁼']),
              ('SW01 w7 H1 SW01', ['KK1⁼']),
              ('w7 H0', ['sH', 'ss'])], maxstates=40000)
T('R17a⁼', 2, [(K01 + ' ' + CK01 + ' ' + K02 + ' ' + K13, None),
               ('w7 H1 w7 H0', ['KK1⁼', 'KK0⁼']),
               (K02 + ' ' + K13 + ' ' + K01 + ' ' + CK01, ['KK1⁼', 'KK0⁼'])], maxstates=40000)
T('R17b⁼', 2, [(K02 + ' ' + K13 + ' ' + K01 + ' ' + CK01, None),
               ('w7 H0 w7 H1', ['KK1⁼', 'KK0⁼']),
               (K01 + ' ' + CK01 + ' ' + K02 + ' ' + K13, ['KK1⁼', 'KK0⁼'])], maxstates=40000)

del OUT[:first]
