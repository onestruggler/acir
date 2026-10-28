"""Runs of D/N8/S314 (new), checked in the model."""
from se_n8lib import *

k = 4
bx0 = G('box', [0], [(1, T_), (2, T_), (3, T_), (4, T_)], True)
eA = G('box', [0], [(1, T_), (3, T_), (4, T_)], True)
B0 = G('box', [0], [(2, T_), (3, T_), (4, T_)], True)
B1 = G('box', [1], [(2, T_), (3, T_), (4, T_)], True)
hgF = G('hg', [0, 1], [(2, T_), (3, T_), (4, T_)], True)
hg01 = G('hg', [0, 1], [(3, T_), (4, T_)], True)
hg02 = G('hg', [0, 2], [(3, T_), (4, T_)], True)
hg12 = G('hg', [1, 2], [(3, T_), (4, T_)], True)
assert swapG(1, hg01) == hg02 and swapG(1, eA) == B0
PP0 = ppL(0)
names = {bx0: 'bx0', eA: 'eA', B0: 'B0', B1: 'B1', hgF: 'hgF', hg01: 'hg01', hg02: 'hg02', hg12: 'hg12',
         SW(0): 'lS0', SW(1): 'lS1', K_(0): 'lK0', C_(0): 'lC0', H_(0): 'lH0', Z_(0): 'lZ0'}
def out(r): print(r.name, lean_steps(r.steps, names))
print('hgPP', eqsem(5, [hgF], PP0 + [bx0] + PP0), eqsem(5, [hg01], PP0 + [eA] + PP0))
# (a) H0 passes hgF
T = [([hgF], PP0 + [bx0] + PP0), ([Z_(0), bx0], [bx0, Z_(0)])]
r = Run(k, T, [H_(0), hgF], '303')
r.rw(1, 0).sem(0, 11, PP0 + [Z_(0)]).rw(10, 1).sem(11, 11, PP0 + [H_(0)]).rw(0, 0, True)
r.expect([hgF, H_(0)]); out(r)
# (b) Z0 passes hgF
T = [([hgF], PP0 + [bx0] + PP0), ([H_(0), bx0], [bx0, H_(0)])]
r = Run(k, T, [Z_(0), hgF], 'Zhg')
r.rw(1, 0).sem(0, 11, PP0 + [H_(0)]).rw(10, 1).sem(11, 11, PP0 + [Z_(0)]).rw(0, 0, True)
r.expect([hgF, Z_(0)]); out(r)
# (c) C0 passes hg12, (d) K0 passes hg12
PP02 = [SW(1)] + PP0 + [SW(1)]
for nm, g, g2, eq in (('282', C_(0), K_(0), ([K_(0), B0], [B0, K_(0)])),
                      ('Khg', K_(0), C_(0), ([C_(0), B0], [B0, C_(0)]))):
    T = [([hg12], [hg02]), sw(1, hg01), ([hg01], PP0 + [eA] + PP0), sw(1, eA), eq]
    r = Run(k, T, [g, hg12], nm)
    r.rw(1, 0).rw(1, 1, True).rw(2, 2).sem(12, 0, [SW(1), SW(1)]).sem(15, 0, [SW(1), SW(1)]).rw(13, 3)
    r.sem(0, 13, PP02 + [g2]).rw(12, 4).sem(13, 13, PP02 + [g])
    r.rw(12, 3, True).sem(14, 2, []).sem(11, 2, []).rw(1, 2, True).rw(0, 1).rw(0, 0, True)
    r.expect([hg12, g]); out(r)
# (e), (f)
for nm, g, eq in (('CB1', C_(0), ([C_(0), B0], [B0, C_(0)])), ('KB1', K_(0), ([K_(0), B0], [B0, K_(0)]))):
    T = [([B1], [B0]), eq]
    r = Run(k, T, [g, B1], nm)
    r.rw(1, 0).rw(0, 1).rw(0, 0, True).expect([B1, g]); out(r)
