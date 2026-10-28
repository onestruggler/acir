"""Runs at width 3 (K = 3, no bulk) for D/N8/T3, checked in the model."""
from se_n8lib import *

E = small_eqs()
k = 2
NS = (3,)
def chk(l, r): return eqsem(3, l, r, Ns=NS)
zxw = [K_(0), SW(0), C_(1), SW(0), K_(0), SW(0), C_(1), SW(0)]
xzw = [SW(0), C_(1), SW(0), K_(0), SW(0), C_(1), SW(0), K_(0)]
W3 = G('zx', [0], [(1, T_), (2, T_)], False); V3 = G('xz', [0], [(1, T_), (2, T_)], False)
B3 = G('box', [0], [(1, T_), (2, T_)], False); C3 = G('box', [1], [(0, T_)], False)
X2 = X_(2)
cL = [SW(0), C_(1), SW(0)]
Bp3 = G('box', [1], [(0, T_), (2, T_)], False)
Bw3 = G('box', [1], [(0, T_), (2, F_)], False)
W1p = G('zx', [0], [(1, T_)], False); V1p = G('xz', [0], [(1, T_)], False)
W1s = E['136'][2]; V1s = E['138'][2]
names = {W3: 'W3', V3: 'V3', B3: 'B3', C3: 'C3', K_(0): 'lK0', SW(0): 'lS0', C_(1): 'lC1',
         Z_(0): 'lZ0', H_(0): 'lH0', Bp3: 'Bp3', Bw3: 'Bw3', W1p: 'W1p', V1p: 'V1p',
         SW(1): 'lS1', Z_(1): 'lZ1'}
def out(r): print(r.name, lean_steps(r.steps, names))
print('defs', chk([W3], zxw), chk([V3], xzw), chk([B3], [C_(1)]), chk([C3], [Z_(0)]))
print('defs2', chk([Bp3], cL), chk([W1p], W1s), chk([V1p], V1s), chk(X2 + [Bp3] + X2, [Bw3]))
assert E['126'][1] == zxw + [Z_(0)] + xzw + [Z_(0)] and E['117'][1] == zxw + xzw
assert E['118'][1] == xzw + zxw
assert E['125'][1] == [Z_(0)] + zxw and E['125'][2] == zxw + [Z_(0), C_(1)]
assert E['128'][1] == cL + zxw and E['128'][2] == zxw + [C_(1)] + cL
assert E['136'][1] == X2 + zxw + X2 + zxw and E['138'][1] == xzw + X2 + xzw + X2

# one table for the width-3 runs
T3 = [([W3], zxw), ([V3], xzw), ([B3], [C_(1)]), ([Bp3], cL), ([W1p], W1s), ([V1p], V1s),
      (E['117'][1], E['117'][2]), (E['118'][1], E['118'][2]), (E['125'][1], E['125'][2]),
      (E['126'][1], E['126'][2]), (E['128'][1], E['128'][2]), (E['136'][1], E['136'][2]),
      (E['138'][1], E['138'][2]), (X2 + [Bp3] + X2, [Bw3])]
I = {n: i for i, n in enumerate(['W3', 'V3', 'B3', 'Bp3', 'W1p', 'V1p', '117', '118', '125', '126',
                                 '128', '136', '138', 'x81'])}

def xcx(r, i):
    """at position i: X2 + cL + X2 -> [Z0] + cL"""
    r.swp(i + 2).swp(i + 1).swp(i).swp(i + 5).swp(i + 6).swp(i + 7)
    r.sem(i + 1, 7, [Z_(1), C_(1)]).sem(i + 2, 0, [SW(0), SW(0)]).sem(i, 3, [Z_(0)])

def xcx_back(r, i):
    """at position i: [Z0] + cL -> X2 + cL + X2"""
    r.sem(i, 1, [SW(0), Z_(1), SW(0)]).sem(i + 2, 2, [])
    r.sem(i + 1, 2, X2 + [C_(1)] + X2)
    r.swp(i).swp(i + 1).swp(i + 2).swp(i + 7).swp(i + 6).swp(i + 5)

r = Run(k, T3, X2 + cL + X2, 'xcx'); xcx(r, 0); r.expect([Z_(0)] + cL)
r = Run(k, T3, [Z_(0)] + cL, 'xcxb'); xcx_back(r, 0); r.expect(X2 + cL + X2)

# (300) at width 3
r = Run(k, T3, [B3], '300_3')
r.rw(0, I['B3']).sem(0, 0, [Z_(0), Z_(0)]).rw(1, I['117'], True).sem(9, 0, [Z_(0), Z_(0)])
r.rw(10, I['118'], True).rw(18, I['126']).sem(18, 2, []).rw(1, I['W3'], True).rw(3, I['V3'], True)
r.sem(0, 1, [C3]).sem(2, 1, [C3]).expect([C3, W3, C3, V3]); out(r)

# (292) at width 3: [W3, Bw3] -> [Bw3, W3]
r = Run(k, T3, [W3, Bw3], '292_3')
r.rw(0, I['W3']).rw(8, I['x81'], True).rw(11, I['Bp3'])
xcx(r, 8)
# zxw + [Z0] + cL
r.sem(9, 0, [C_(1), C_(1)]).rw(0, I['125'], True)
# [Z0] + zxw + [C1] + cL
r.rw(1, I['128'], True)
# [Z0] + cL + zxw
r.rw(4, I['W3'], True)
xcx_back(r, 0)
r.rw(3, I['Bp3'], True).rw(0, I['x81'])
r.expect([Bw3, W3]); out(r)

# [cL, Wb] -> [Wb, cL] with Wb = X2 + zxw + X2 (the core of (305))
r = Run(k, T3, cL + X2 + zxw + X2, 'cWb')
# cL + X2 -> X2 + [Z0] + cL : insert X2 X2 before cL, then xcx
r.sem(0, 0, X2 + X2)
xcx(r, 3)
# X2 + [Z0] + cL + zxw + X2
r.rw(4, I['128'])
# X2 + [Z0] + zxw + [C1] + cL + X2
r.rw(3, I['125'])
# X2 + zxw + [Z0, C1, C1] + cL + X2
r.sem(12, 2, [])
# X2 + zxw + [Z0] + cL + X2
xcx_back(r, 11)
# X2 + zxw + X2 + cL + X2 + X2
r.sem(17, 6, [])
r.expect(X2 + zxw + X2 + cL); out(r)

# (305) at width 3: [V1p, Bp3, W1p, Bp3] -> [B3]
TcWb = T3 + [(cL + X2 + zxw + X2, X2 + zxw + X2 + cL)]
r = Run(k, TcWb, [V1p, Bp3, W1p, Bp3], '305_3')
r.rw(0, I['V1p']).rw(8, I['Bp3']).rw(11, I['W1p']).rw(19, I['Bp3'])
# V1s + cL + W1s + cL
r.rw(0, I['138'], True).rw(25, I['136'], True)
# xzw + X2 + xzw + X2 + cL + X2 + zxw + X2 + zxw + cL
r.rw(22, len(T3))
# xzw + X2 + xzw + X2 + X2 + zxw + X2 + cL + zxw + cL
r.sem(19, 6, []).rw(11, I['118']).sem(8, 6, [])
# xzw + cL + zxw + cL
r.rw(8, I['128'])
# xzw + zxw + [C1] + cL + cL
r.sem(19, 2, []).sem(18, 2, []).sem(17, 2, []).rw(0, I["118"]).rw(0, I["B3"], True)
r.expect([B3]); out(r)
