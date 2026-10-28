"""Runs of D/N8/S290 (new), checked in the model."""
from se_n8lib import *

k = 4
bx0 = G('box', [0], [(1, T_), (2, T_), (3, T_), (4, T_)], True)
wW = G('zx', [0], [(1, T_), (2, T_)], False); wV = G('xz', [0], [(1, T_), (2, T_)], False)
cC = G('box', [1], [(0, T_), (3, T_), (4, T_)], True)
eA = G('box', [0], [(1, T_), (3, T_), (4, T_)], True)
c3 = G('box', [3], [(0, T_), (2, T_)], False)
Z123 = G('zx', [0], [(1, T_), (2, T_), (3, T_)], False)
X123 = G('xz', [0], [(1, T_), (2, T_), (3, T_)], False)
A2z = G('zx', [1], [(0, T_), (2, T_), (3, T_)], False)
A2x = G('xz', [1], [(0, T_), (2, T_), (3, T_)], False)
D4 = G('box', [0], [(1, T_), (4, T_)], True)
D3w = G('box', [0], [(1, T_), (3, F_), (4, T_)], True)
Zw = G('zx', [0], [(1, T_), (2, T_), (3, F_)], False)
Bx2w = G('box', [0], [(1, T_), (2, F_), (3, T_), (4, T_)], True)
Wb = G('zx', [0], [(1, T_), (2, F_)], False); Vb = G('xz', [0], [(1, T_), (2, F_)], False)
Bw = G('box', [1], [(0, T_), (2, F_), (3, T_), (4, T_)], True)
Bf = G('box', [1], [(0, T_), (2, T_), (3, T_), (4, T_)], True)
Wt = G('zx', [1], [(0, T_), (2, F_)], False); Vt = G('xz', [1], [(0, T_), (2, F_)], False)
wW1 = G('zx', [1], [(0, T_), (2, T_)], False); wV1 = G('xz', [1], [(0, T_), (2, T_)], False)
W1 = G('zx', [0], [(1, T_)], False); V1 = G('xz', [0], [(1, T_)], False)
names = {bx0: 'bx0', wW: 'wW', wV: 'wV', cC: 'cC', eA: 'eA', c3: 'c3', Z123: 'Z123', X123: 'X123',
         A2z: 'A2z', A2x: 'A2x', D4: 'D4', D3w: 'D3w', Zw: 'Zw', Bx2w: 'Bx2w', Wb: 'Wb', Vb: 'Vb',
         Bw: 'Bw', Bf: 'bx1p', Wt: 'Wt', Vt: 'Vt', wW1: 'wW1', wV1: 'wV1', W1: 'W1', V1: 'V1',
         SW(0): 'lS0', SW(1): 'lS1', K_(0): 'lK0', C_(0): 'lC0', H_(0): 'lH0', SW(2): 'lS2'}
assert swapG(0, cC) == eA and swapG(0, A2z) == Z123 and swapG(0, A2x) == X123
assert swapG(0, Bx2w) == Bw and swapG(0, bx0) == Bf and swapG(0, Wb) == Wt and swapG(0, Vb) == Vt
assert swapG(0, wW) == wW1 and swapG(0, wV) == wV1 and swapG(2, D4) == D4
def out(r): print(r.name, lean_steps(r.steps, names))

# (291i)
T291i = [sw(0, cC), sw(0, A2z), ([A2z, cC], [cC, A2z])]
r = Run(k, T291i, [eA, Z123], '291i')
r.rw(0, 0, True).rw(3, 1, True).sem(2, 2, []).rw(1, 2, True).sem(2, 0, [SW(0), SW(0)])
r.rw(0, 1).rw(1, 0).expect([Z123, eA]); out(r)

# (291x)
T291x = [([eA, Z123], [Z123, eA])]
r = Run(k, T291x, [eA, X123], '291x')
r.sem(0, 0, [X123, Z123]).rw(1, 0, True).sem(2, 2, []).expect([X123, eA]); out(r)

# (290)
print('D4 merge', eqsem(5, [D4], [eA, D3w]))
print('Zw split', eqsem(5, [Zw], [wW, X123]), eqsem(5, [Zw], [X123, wW]))
T290 = [([eA, Z123], [Z123, eA]), ([eA, X123], [X123, eA]), ([eA, wW], [wW, eA]),
        (X_(3) + [eA] + X_(3), [D3w])]
r = Run(k, T290, [D4, Z123], '290')
r.sem(0, 1, [eA, D3w]).rw(1, 3, True).sem(5, 4, [Zw] + X_(3)).sem(5, 1, [wW, X123])
r.rw(4, 2, False).rw(5, 1, False).sem(4, 2, [Zw]).sem(1, 4, [Z123] + X_(3)).rw(2, 3, False)
r.rw(0, 0, False).sem(1, 2, [D4]).expect([Z123, D4]); out(r)

# (290w)
T290w = [([D4, Z123], [Z123, D4]), ([D4, H_(3)], [H_(3), D4]), ([D4, Z_(3)], [Z_(3), D4])]
r = Run(k, T290w, [D4, Zw], '290w')
r.sem(1, 1, X_(3) + [Z123] + X_(3)).rw(0, 1).rw(1, 2).rw(2, 1).rw(3, 0)
r.rw(4, 1).rw(5, 2).rw(6, 1).sem(0, 7, [Zw]).expect([Zw, D4]); out(r)

# (295i)
F295 = [wW, A2z, D4, A2x, wV, A2z, D4, A2x]
F295i = [Z123, A2z, D4, A2x, X123, A2z, D4, A2x]
print('wW split', eqsem(5, [wW], [Z123, Zw]))
T295i = [([bx0], F295), ([D4, Zw], [Zw, D4])]
r = Run(k, T295i, [bx0], '295i')
r.rw(0, 0).sem(0, 1, [Z123, Zw]).sem(1, 2, [A2z, Zw]).rw(2, 1, True).sem(3, 2, [A2x, Zw])
r.sem(4, 2, [X123]).expect(F295i); out(r)

# (306)
T306 = [([bx0], F295i), sw(2, D4)]
r = Run(k, T306, [bx0, SW(2)], '306')
r.rw(0, 0)
for i in range(7, -1, -1):
    x = r.cur[i]
    if x == D4:
        r.sem(i, 0, [SW(2), SW(2)]).rw(i + 1, 1)
    else:
        r.sem(i, 2, [SW(2), x])
r.rw(1, 0, True).expect([SW(2), bx0]); out(r)

# (269w): Bx2w = [Wb, cC, Vb, cC]
T269w = [(X_(2) + [bx0] + X_(2), [Bx2w]), ([bx0], [wW, cC, wV, cC]),
         ([cC, H_(2)], [H_(2), cC]), ([cC, Z_(2)], [Z_(2), cC])]
r = Run(k, T269w, [Bx2w], '269w')
r.rw(0, 0, True).rw(3, 1).sem(0, 4, [Wb] + X_(2)).rw(3, 2, True).rw(2, 3, True).rw(1, 2, True)
# [Wb cC H2 Z2 H2 wV cC H2 Z2 H2]
r.sem(2, 4, [Vb] + X_(2)).rw(5, 2, True).rw(4, 3, True).rw(3, 2, True).sem(4, 6, [])
r.expect([Wb, cC, Vb, cC]); out(r)

# (269Bw): Bw = [Wt, eA, Vt, eA]
T269Bw = [([Bx2w], [Wb, cC, Vb, cC]), sw(0, Bx2w), sw(0, Wb), sw(0, cC), sw(0, Vb)]
r = Run(k, T269Bw, [Bw], '269Bw')
r.rw(0, 1, True).rw(1, 0)
for i in (2, 5, 8):
    r.sem(i, 0, [SW(0), SW(0)])
# [S0 Wb S0 S0 cC S0 S0 Vb S0 S0 cC S0]
r.rw(0, 2).rw(1, 3).rw(2, 4).rw(3, 3).expect([Wt, eA, Vt, eA]); out(r)

# (292): [wW, Bw] = [Bw, wW]
T292 = [([Bw], [Wt, eA, Vt, eA]), ([eA, wW], [wW, eA])]
r = Run(k, T292, [wW, Bw], '292')
r.rw(1, 0).sem(0, 2, [Wt, wW]).rw(1, 1, True).sem(2, 2, [Vt, wW]).rw(3, 1, True).rw(0, 0, True)
r.expect([Bw, wW]); out(r)

# (287) white: [eA, Wb] = [Wb, eA], [eA, Vb] = [Vb, eA]
for nm, g, gb in (('287w', wW, Wb), ('287vw', wV, Vb)):
    T = [([eA, g], [g, eA]), ([eA, H_(2)], [H_(2), eA]), ([eA, Z_(2)], [Z_(2), eA])]
    r = Run(k, T, [eA, gb], nm)
    r.sem(1, 1, X_(2) + [g] + X_(2)).rw(0, 1).rw(1, 2).rw(2, 1).rw(3, 0)
    r.rw(4, 1).rw(5, 2).rw(6, 1).sem(0, 7, [gb]).expect([gb, eA]); out(r)

# Wb, Vb pass Bf
T269f = [([bx0], [wW, cC, wV, cC]), sw(0, bx0), sw(0, wW), sw(0, cC), sw(0, wV)]
r = Run(k, T269f, [Bf], '269f')
r.rw(0, 1, True).rw(1, 0)
for i in (2, 5, 8):
    r.sem(i, 0, [SW(0), SW(0)])
r.rw(0, 2).rw(1, 3).rw(2, 4).rw(3, 3).expect([wW1, eA, wV1, eA]); out(r)
for nm, gb in (('WbBf', Wb), ('VbBf', Vb)):
    T = [([Bf], [wW1, eA, wV1, eA]), ([eA, gb], [gb, eA])]
    r = Run(k, T, [gb, Bf], nm)
    r.rw(1, 0).sem(0, 2, [wW1, gb]).rw(1, 1, True).sem(2, 2, [wV1, gb]).rw(3, 1, True).rw(0, 0, True)
    r.expect([Bf, gb]); out(r)

# Bw Bw = 1
TBw2 = [sw(0, Bx2w), (X_(2) + [bx0] + X_(2), [Bx2w]), ([bx0, bx0], [])]
r = Run(k, TBw2, [Bw, Bw], 'Bw2')
r.rw(0, 0, True).rw(3, 0, True).sem(2, 2, []).rw(1, 1, True).rw(8, 1, True).sem(5, 6, [])
r.rw(4, 2).sem(1, 6, []).sem(0, 2, []).expect([]); out(r)

# (301) and (302) relabeled: [Bf, Bw] = [cC], [Bw, Bf] = [cC]
for nm, a, b, e in (('301r', Bf, Bw, ([bx0, Bx2w], [eA])), ('302r', Bw, Bf, ([Bx2w, bx0], [eA]))):
    T = [sw(0, bx0), sw(0, Bx2w), e, sw(0, eA)]
    r = Run(k, T, [a, b], nm)
    ia, ib = (0, 1) if a == Bf else (1, 0)
    r.rw(0, ia, True).rw(3, ib, True).sem(2, 2, []).rw(1, 2).rw(0, 3).expect([cC]); out(r)

# (305): [V1, Bf, W1, Bf] = [bx0]
print('V1 split', eqsem(5, [V1], [wV, Vb]), 'W1 split', eqsem(5, [W1], [Wb, wW]))
T305 = [([Vb, Bf], [Bf, Vb]), ([Bw, Bw], []), ([wW, Bw], [Bw, wW]), ([Bf, Bw], [cC]),
        ([Bw, Bf], [cC]), ([bx0], [wV, cC, wW, cC])]
r = Run(k, T305, [V1, Bf, W1, Bf], '305')
r.sem(0, 1, [wV, Vb]).sem(3, 1, [Wb, wW]).rw(1, 0).sem(2, 2, [])
# [wV, Bf, wW, Bf]
r.rw(2, 1, True).rw(3, 2, True).rw(1, 3).rw(3, 4).rw(0, 5, True).expect([bx0]); out(r)
