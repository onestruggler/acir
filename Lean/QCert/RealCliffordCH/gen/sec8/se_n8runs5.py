"""Runs at width 4 (the fixed-width engine WEng, M = 3) for D/N8/T4, checked in the model."""
from se_n8lib import *

import se_n8lib
tok = se_n8lib._tok()
G4, P4, S4 = tok.G, tok.P, tok.S
M = 3
T, F = True, False

def tS(j): return S4('S', j)
def tH(j): return S4('H', j)
def tZ(j): return S4('Z', j)
def tC(j): return S4('C', j)
def tK(j): return S4('K', j)
def tX(j): return [tH(j), tZ(j), tH(j)]

bx = G4('box', [0], [(1, T), (2, T), (3, T)])
W = G4('zx', [0], [(1, T), (2, T)]); V = G4('xz', [0], [(1, T), (2, T)])
C = G4('box', [1], [(0, T), (3, T)])
cz02 = P4(2, [('C', 0)], [0, 2]); cz03 = P4(2, [('C', 0)], [0, 3])
cz01p = P4(2, [('C', 0)], [0, 1]); cz13 = P4(2, [('C', 0)], [1, 3]); cz23p = P4(2, [('C', 0)], [2, 3])
bxf = tok.relabel(bx, 0)          # box on wire 1, controls 0, 2, 3
eA = tok.relabel(C, 0)            # box on wire 0, controls 1, 3
D = G4('box', [0], [(1, T)])
Z123 = G4('zx', [0], [(1, T), (2, T), (3, T)]); X123 = G4('xz', [0], [(1, T), (2, T), (3, T)])
Bx2w = G4('box', [0], [(1, T), (2, F), (3, T)])
Bw = tok.relabel(Bx2w, 0)
Wb = G4('zx', [0], [(1, T), (2, F)]); Vb = G4('xz', [0], [(1, T), (2, F)])
Wt = tok.relabel(Wb, 0); Vt = tok.relabel(Vb, 0)
W1 = G4('zx', [0], [(1, T)]); V1 = G4('xz', [0], [(1, T)])
names = {bx: 'bx4', W: 'W4', V: 'V4', C: 'C4', cz02: 'cz02', cz03: 'cz03', cz01p: 'cz01p', cz13: 'cz13',
         cz23p: 'cz23p', bxf: 'bxf4', eA: 'eA4', D: 'D44', Z123: 'Z1234', X123: 'X1234', Bx2w: 'Bx2w4',
         Bw: 'Bw4', Wb: 'Wb4', Vb: 'Vb4', Wt: 'Wt4', Vt: 'Vt4', W1: 'W14', V1: 'V14'}
for j in range(4):
    names.update({tS(j): 'wS%d' % j, tH(j): 'wH%d' % j, tZ(j): 'wZ%d' % j, tC(j): 'wC%d' % j,
                  tK(j): 'wK%d' % j})
def out(r): print(r.name, wlean_steps(r.steps, names))
def eq4(a, b): return tok.weq(4, a, b)

print('checks', eq4([Z123], [tK(0), bxf, tK(0), bxf]), eq4([X123], [bxf, tK(0), bxf, tK(0)]),
      eq4([bx], [W, C, V, C]), eq4([D], [tZ(1)]), eq4(tX(2) + [bx] + tX(2), [Bx2w]))

# the table: W4/A results and (269), (81)
T4 = [([tZ(0), bx], [bx, tZ(0)]),            # 0 t154
      ([tH(0), bx], [bx, tH(0)]),            # 1 t155
      ([tS(1), bx, tS(1)], [bx]),            # 2 t157
      ([cz02, bx], [bx, cz02]),              # 3 t159
      ([tS(2), bx, tS(2)], [bx]),            # 4 t161
      ([bx], [W, C, V, C]),                  # 5 (269)
      (tX(2) + [bx] + tX(2), [Bx2w]),        # 6 (81)
      ([Z123], [tK(0), bxf, tK(0), bxf]),    # 7 definition
      ([X123], [bxf, tK(0), bxf, tK(0)])]    # 8 definition

# R1: cz03 passes bx
r = WRun(M, T4, [cz03, bx], 'R1')
r.swp(0, 2, cz02, cz03, True).rw(3, 4, True).sem(2, 2, []).rw(1, 3).sem(2, 0, [tS(2), tS(2)])
r.rw(0, 4).swp(1, 2, cz02, cz03).expect([bx, cz03]); out(r)
T4 += [([cz03, bx], [bx, cz03])]             # 9

# R3: (300)
r = WRun(M, T4, [bx], 'R3')
r.sem(0, 0, [C, C]).sem(1, 1, [cz03]).rw(1, 9).sem(2, 1, [C]).rw(1, 5).sem(4, 2, [])
r.expect([C, W, C, V]); out(r)
T4 += [([bx], [C, W, C, V])]                 # 10

# R4: (299)
r = WRun(M, T4, [bx, bx], 'R4')
r.rw(0, 5).rw(4, 10).sem(3, 2, []).sem(2, 2, []).sem(1, 2, []).sem(0, 2, []).expect([]); out(r)
T4 += [([bx, bx], [])]                       # 11

# R5: (290): [D, Z123] -> [Z123, D]
r = WRun(M, T4, [D, Z123], 'R5')
r.sem(0, 1, [tZ(1)]).rw(1, 7).sem(0, 2, [tK(0), tZ(1)])
# [K0, Z1, bxf, K0, bxf]
r.sem(1, 1, [tS(0), tZ(0), tS(0)]).swp(4, 0, bx, bxf, True)
# [K0, S0, Z0, S0, S0, bx, S0, K0, bxf]
r.sem(3, 2, []).rw(2, 0).sem(3, 0, [tS(0), tS(0)]).swp(1, 0, bx, bxf).sem(2, 3, [tZ(1)])
# [K0, bxf, Z1, K0, bxf]
r.sem(2, 2, [tK(0), tZ(1)])
r.sem(3, 1, [tS(0), tZ(0), tS(0)]).swp(6, 0, bx, bxf, True).sem(5, 2, []).rw(4, 0)
r.sem(5, 0, [tS(0), tS(0)]).swp(3, 0, bx, bxf).sem(4, 3, [tZ(1)])
r.rw(0, 7, True).sem(1, 1, [D]).expect([Z123, D]); out(r)

T4 += [([bx], [C, W, C, V]) if False else ([cz02, cz03], [cz03, cz02])]   # 12 (placeholder: CZ02/CZ03 commute)
# eAbxf: [eA, bxf] -> [bxf, eA]
r = WRun(M, T4, [eA, bxf], 'eAbxf')
r.swp(0, 0, C, eA, True).swp(3, 0, bx, bxf, True).sem(2, 2, []).sem(1, 1, [cz03]).rw(1, 9)
r.sem(2, 1, [C]).sem(2, 0, [tS(0), tS(0)]).swp(0, 0, bx, bxf).swp(1, 0, C, eA)
r.expect([bxf, eA]); out(r)
T4 += [([eA, bxf], [bxf, eA])]               # 13
# R6: (291)
r = WRun(M, T4, [eA, Z123], 'R6')
r.rw(1, 7).sem(0, 2, [tK(0), eA]).rw(1, 13).sem(2, 2, [tK(0), eA]).rw(3, 13).rw(0, 7, True)
r.expect([Z123, eA]); out(r)
# 272r: [eA, cz02] -> [cz02, eA]
r = WRun(M, T4, [eA, cz02], '272r')
r.sem(0, 1, [cz13]).sem(0, 0, [tS(1), tS(1)]).sem(3, 0, [tS(1), tS(1)]).sem(6, 0, [tS(1), tS(1)])
r.swp(1, 1, cz13, cz23p).swp(2, 1, cz02, cz01p)
r.sem(1, 1, [tC(2)]).sem(2, 1, [tC(0)]).swp_(1).sem(1, 1, [cz01p]).sem(2, 1, [cz23p])
r.swp(1, 1, cz02, cz01p, True).swp(4, 1, cz13, cz23p, True).sem(0, 2, []).sem(1, 2, []).sem(2, 2, []).sem(1, 1, [eA])
r.expect([cz02, eA]); out(r)
T4 += [([eA, cz02], [cz02, eA])]             # 14
# 287: [eA, W] -> [W, eA]; 287v: [eA, V] -> [V, eA]
r = WRun(M, T4, [eA, W], '287_4')
r.sem(1, 1, [tK(0), cz02, tK(0), cz02]).sem(0, 2, [tK(0), eA]).rw(1, 14).sem(2, 2, [tK(0), eA]).rw(3, 14)
r.sem(0, 4, [W]).expect([W, eA]); out(r)
T4 += [([eA, W], [W, eA])]                   # 15
r = WRun(M, T4, [eA, V], '287v_4')
r.sem(1, 1, [cz02, tK(0), cz02, tK(0)]).rw(0, 14).sem(1, 2, [tK(0), eA]).rw(2, 14).sem(3, 2, [tK(0), eA])
r.sem(0, 4, [V]).expect([V, eA]); out(r)
T4 += [([eA, V], [V, eA])]                   # 16
# 269w: [Bx2w] -> [Wb, C, Vb, C]
def xpastC(r, i):
    """at i: X2 + [C] -> [C] + X2"""
    r.sem(i + 3, 1, [cz03]).sem(i, 4, [cz03] + tX(2)).sem(i, 1, [C])
r = WRun(M, T4, [Bx2w], '269w_4')
r.rw(0, 6, True).rw(3, 5).sem(0, 4, [Wb] + tX(2))
xpastC(r, 1)
r.sem(2, 4, [Vb] + tX(2)); xpastC(r, 3); r.sem(4, 6, [])
r.expect([Wb, C, Vb, C]); out(r)
T4 += [([Bx2w], [Wb, C, Vb, C])]             # 17
# 269Bw
r = WRun(M, T4, [Bw], '269Bw_4')
r.swp(0, 0, Bx2w, Bw, True).rw(1, 17)
for i in (2, 5, 8): r.sem(i, 0, [tS(0), tS(0)])
r.swp(0, 0, Wb, Wt).swp(1, 0, C, eA).swp(2, 0, Vb, Vt).swp(3, 0, C, eA)
r.expect([Wt, eA, Vt, eA]); out(r)
T4 += [([Bw], [Wt, eA, Vt, eA])]             # 18
# R7: (292)
r = WRun(M, T4, [W, Bw], 'R7')
r.rw(1, 18).sem(0, 2, [Wt, W]).rw(1, 15, True).sem(2, 2, [Vt, W]).rw(3, 15, True).rw(0, 18, True)
r.expect([Bw, W]); out(r)
T4 += [([W, Bw], [Bw, W])]                   # 19

# (300w): [Bx2w] -> [C, Wb, C, Vb]
r = WRun(M, T4, [Bx2w], '300w_4')
r.rw(0, 6, True).rw(3, 10); xpastC(r, 0); r.sem(1, 4, [Wb] + tX(2)); xpastC(r, 2)
r.sem(3, 7, [Vb]).expect([C, Wb, C, Vb]); out(r)
T4 += [([Bx2w], [C, Wb, C, Vb])]             # 20
print('C W1 C', eq4([C, W1, C], [eA, W1]))
# R8: (301): [bx, Bx2w] -> [eA]
r = WRun(M, T4, [bx, Bx2w], 'R8')
r.rw(0, 5).rw(4, 20).sem(3, 2, []).sem(2, 2, [cz02, W1, cz02])
r.sem(1, 1, [cz03]).sem(1, 2, [cz02, cz03]).sem(2, 1, [C])
r.sem(5, 1, [cz03]).sem(4, 2, [cz03, cz02]).sem(4, 1, [C])
r.sem(2, 3, [eA, W1]).rw(1, 14, True).rw(0, 15, True).sem(1, 5, [])
r.expect([eA]); out(r)
T4 += [([bx, Bx2w], [eA])]                   # 21
T4 += [(tX(2) + [Bx2w] + tX(2), [bx])]       # 22 (81)
# R8b: (302): [Bx2w, bx] -> [eA]
r = WRun(M, T4, [Bx2w, bx], 'R8b')
r.rw(0, 6, True).rw(7, 22, True).sem(4, 6, []).rw(3, 21).sem(3, 1, [cz13]).sem(0, 7, [cz13]).sem(0, 1, [eA])
r.expect([eA]); out(r)
T4 += [([Bx2w, bx], [eA])]                   # 23
# 269f: [bxf] -> [wW1, eA, wV1, eA]
wW1 = tok.relabel(W, 0); wV1 = tok.relabel(V, 0)
names.update({wW1: 'wW14', wV1: 'wV14'})
r = WRun(M, T4, [bxf], '269f_4')
r.swp(0, 0, bx, bxf, True).rw(1, 5)
for i in (2, 5, 8): r.sem(i, 0, [tS(0), tS(0)])
r.swp(0, 0, W, wW1).swp(1, 0, C, eA).swp(2, 0, V, wV1).swp(3, 0, C, eA)
r.expect([wW1, eA, wV1, eA]); out(r)
T4 += [([bxf], [wW1, eA, wV1, eA])]          # 24
# 287vw: [eA, Vb] -> [Vb, eA]
r = WRun(M, T4, [eA, Vb], '287vw_4')
r.sem(1, 1, tX(2) + [V] + tX(2)).sem(0, 1, [cz13]).sem(0, 4, tX(2) + [cz13]).sem(3, 1, [eA]).rw(3, 16)
r.sem(5, 1, [cz13]).sem(5, 4, tX(2) + [cz13]).sem(8, 1, [eA]).sem(0, 8, [Vb])
r.expect([Vb, eA]); out(r)
T4 += [([eA, Vb], [Vb, eA])]                 # 25
# VbBf: [Vb, bxf] -> [bxf, Vb]
r = WRun(M, T4, [Vb, bxf], 'VbBf_4')
r.rw(1, 24).sem(0, 2, [wW1, Vb]).rw(1, 25, True).sem(2, 2, [wV1, Vb]).rw(3, 25, True).rw(0, 24, True)
r.expect([bxf, Vb]); out(r)
T4 += [([Vb, bxf], [bxf, Vb])]               # 26
# Bw2: [Bw, Bw] -> []
r = WRun(M, T4, [Bw, Bw], 'Bw2_4')
r.swp(0, 0, Bx2w, Bw, True).swp(3, 0, Bx2w, Bw, True).sem(2, 2, []).rw(1, 6, True).rw(8, 6, True)
r.sem(5, 6, []).rw(4, 11).sem(1, 6, []).sem(0, 2, [])
r.expect([]); out(r)
T4 += [([Bw, Bw], [])]                       # 27
# 301r, 302r
r = WRun(M, T4, [bxf, Bw], '301r_4')
r.swp(0, 0, bx, bxf, True).swp(3, 0, Bx2w, Bw, True).sem(2, 2, []).rw(1, 21).swp(0, 0, eA, C)
r.expect([C]); out(r)
T4 += [([bxf, Bw], [C])]                     # 28
r = WRun(M, T4, [Bw, bxf], '302r_4')
r.swp(0, 0, Bx2w, Bw, True).swp(3, 0, bx, bxf, True).sem(2, 2, []).rw(1, 23).swp(0, 0, eA, C)
r.expect([C]); out(r)
T4 += [([Bw, bxf], [C])]                     # 29
# 286: [bx] -> [V, C, W, C]
r = WRun(M, T4, [bx], '286_4')
r.sem(0, 0, [tZ(0), tZ(0)]).rw(1, 0).rw(1, 5).sem(0, 2, [V, tZ(0)]).sem(1, 2, [C, tZ(0)])
r.sem(2, 2, [W, tZ(0)]).sem(3, 3, [C])
r.expect([V, C, W, C]); out(r)
T4 += [([bx], [V, C, W, C])]                 # 30
# R9: (305): [V1, bxf, W1, bxf] -> [bx]
r = WRun(M, T4, [V1, bxf, W1, bxf], 'R9')
r.sem(0, 1, [V, Vb]).sem(3, 1, [Wb, W]).rw(1, 26).sem(2, 2, []).rw(2, 27, True).rw(3, 19, True)
r.rw(1, 28).rw(3, 29).rw(0, 30, True)
r.expect([bx]); out(r)
