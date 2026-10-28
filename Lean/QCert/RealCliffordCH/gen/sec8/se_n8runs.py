"""Runs of D/N8 (new modules), checked in the model."""
from se_n8lib import *

k = 4
bx0 = G('box', [0], [(1, T_), (2, T_), (3, T_), (4, T_)], True)
wW = G('zx', [0], [(1, T_), (2, T_)], False); wV = G('xz', [0], [(1, T_), (2, T_)], False)
cC = G('box', [1], [(0, T_), (3, T_), (4, T_)], True)
eA = G('box', [0], [(1, T_), (3, T_), (4, T_)], True)
c3 = G('box', [3], [(0, T_), (2, T_)], False)
lK0 = K_(0)
names = {bx0: 'bx0', wW: 'wW', wV: 'wV', cC: 'cC', eA: 'eA', c3: 'c3', lK0: 'lK0'}

# (287): eA passes wW
T287 = [([c3, eA], [eA, c3])]
r = Run(k, T287, [eA, wW], '287')
r.sem(1, 1, [lK0, c3, lK0, c3]).sem(0, 2, [lK0, eA]).rw(1, 0, True).sem(2, 2, [lK0, eA]).rw(3, 0, True)
r.sem(0, 4, [wW]).expect([wW, eA])
print(lean_steps(r.steps, names))
# (287) for wV
r = Run(k, T287, [eA, wV], '287v')
r.sem(1, 1, [c3, lK0, c3, lK0]).rw(0, 0, False).sem(1, 2, [lK0, eA]).rw(2, 0, True).sem(3, 2, [lK0, eA])
r.sem(0, 4, [wV]).expect([wV, eA])
print(lean_steps(r.steps, names))

# (287) for wV (fixed)
r = Run(k, T287, [eA, wV], '287v')
r.sem(1, 1, [c3, lK0, c3, lK0]).rw(0, 0, True).sem(1, 2, [lK0, eA]).rw(2, 0, True).sem(3, 2, [lK0, eA])
r.sem(0, 4, [wV]).expect([wV, eA])
print(lean_steps(r.steps, names))

# (300): bx0 = [cC, wW, cC, wV]
T300 = [([bx0], [wW, cC, wV, cC]), ([bx0, bx0], [])]
r = Run(k, T300, [bx0], '300')
r.sem(0, 0, [cC, cC]).sem(1, 0, [wW, wV]).sem(2, 0, [cC, cC]).sem(3, 0, [wV, wW])
r.rw(4, 0, True).rw(4, 1, False).expect([cC, wW, cC, wV])
print(lean_steps(r.steps, names))

# (81) letters
Bx2w = G('box', [0], [(1, T_), (2, F_), (3, T_), (4, T_)], True)
Wb = G('zx', [0], [(1, T_), (2, F_)], False); Vb = G('xz', [0], [(1, T_), (2, F_)], False)
names.update({Bx2w: 'Bx2w', Wb: 'Wb', Vb: 'Vb'})
print('81 check', eqsem(5, X_(2) + [bx0] + X_(2), [Bx2w]))
# (300w): Bx2w = [cC, Wb, cC, Vb]
T300w = [(X_(2) + [bx0] + X_(2), [Bx2w]), ([bx0], [cC, wW, cC, wV]),
         ([cC, H_(2)], [H_(2), cC]), ([cC, Z_(2)], [Z_(2), cC])]
r = Run(k, T300w, [Bx2w], '300w')
r.rw(0, 0, True).rw(3, 1, False)
# [H2 Z2 H2 cC wW cC wV H2 Z2 H2]: move the left X2 right through cC
r.rw(2, 2, True).rw(1, 3, True).rw(0, 2, True)
# [cC H2 Z2 H2 wW cC wV H2 Z2 H2]
r.sem(1, 4, [Wb] + X_(2))
# [cC Wb H2 Z2 H2 cC wV H2 Z2 H2]
r.rw(4, 2, True).rw(3, 3, True).rw(2, 2, True)
r.sem(3, 7, [Vb])
r.expect([cC, Wb, cC, Vb])
print(lean_steps(r.steps, names))

# (301): [bx0, Bx2w] = [eA]
W1 = G('zx', [0], [(1, T_)], False); V1 = G('xz', [0], [(1, T_)], False)
cz02L = [SW(1), C_(0), SW(1)]
names.update({W1: 'W1', V1: 'V1'})
print('cCW1cC', eqsem(5, [cC, W1, cC], [eA, W1]), eqsem(5, [cC, W1, cC], [W1, eA]))
T301 = [([bx0], [wW, cC, wV, cC]), ([Bx2w], [cC, Wb, cC, Vb]), (cz02L + [cC], [cC] + cz02L),
        ([c3, eA], [eA, c3]), ([eA, wW], [wW, eA])]
r = Run(k, T301, [bx0, Bx2w], '301')
r.rw(0, 0).rw(4, 1).sem(3, 2, []).sem(2, 2, cz02L + [W1] + cz02L)
r.rw(1, 2, True).rw(6, 2, False)
r.sem(4, 3, [eA, W1])
r.sem(1, 3, [c3]).rw(1, 3, False).rw(0, 4, True)
r.sem(1, len(r.cur) - 1, [])
r.expect([eA])
print(lean_steps(r.steps, names))

# (302): [Bx2w, bx0] = [eA]
T302 = [(X_(2) + [bx0] + X_(2), [Bx2w]), (X_(2) + [Bx2w] + X_(2), [bx0]), ([bx0, Bx2w], [eA]),
        ([eA, H_(2)], [H_(2), eA]), ([eA, Z_(2)], [Z_(2), eA])]
r = Run(k, T302, [Bx2w, bx0], '302')
r.rw(0, 0, True).rw(7, 1, True).sem(4, 6, []).rw(3, 2)
r.rw(2, 3, True).rw(1, 4, True).rw(0, 3, True).sem(1, 6, [])
r.expect([eA])
print(lean_steps(r.steps, names))
