import sys
from fractions import Fraction as F
from lat4 import G, e8_roots
import ss
R = []
for r in e8_roots():
    R.append(tuple(int(2 * x) for x in r) + (0,) * 8)
    R.append((0,) * 8 + tuple(int(2 * x) for x in r))
idx = {v: i for i, v in enumerate(R)}
def act(g, v):
    w = G[g](tuple(F(x, 2) for x in v))
    return tuple(int(2 * x) for x in w)
VG = ['X0', 'X1', 'X2', 'X3', 'CX0', 'HH0', 'SW0', 'CX1', 'HH1', 'SW1', 'CX2', 'CCX0', 'CCX1']
perms = [tuple(idx[act(g, v)] for v in R) for g in VG]
o = ss.order(perms)
print('|V| =', o)
from math import factorial
w = 696729600
print('|W(E8)|^2 * 2 =', 2 * w * w, ' ratio', 2 * w * w / o)
