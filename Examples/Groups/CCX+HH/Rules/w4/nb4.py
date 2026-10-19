"""Neighbours of L = E8+E8 under the step HH2: the V-orbit of HH2 L."""
import time
from lat4 import G, basis_E8E8, e8_roots
from fractions import Fraction as F

R = []
for r in e8_roots():
    R.append(r + (F(0),) * 8)
    R.append((F(0),) * 8 + r)
L0 = frozenset(R)
VG = ['X0', 'X1', 'X2', 'X3', 'CX0', 'HH0', 'SW0', 'CX1', 'HH1', 'SW1', 'CX2', 'CCX0', 'CCX1']
for g in VG:
    assert frozenset(G[g](v) for v in L0) == L0, g
start = frozenset(G['HH2'](v) for v in L0)
assert start != L0
seen = {start}
fr = [start]
t0 = time.time()
while fr:
    new = []
    for S in fr:
        for g in VG:
            T = frozenset(G[g](v) for v in S)
            if T not in seen:
                seen.add(T); new.append(T)
    fr = new
    print('orbit so far', len(seen), round(time.time() - t0), flush=True)
    if len(seen) > 200000:
        break
print('V-orbit of HH2 L:', len(seen))
