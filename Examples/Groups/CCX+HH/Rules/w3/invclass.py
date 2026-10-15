import sys
sys.path.insert(0, '..')
from e8 import root_orbit, ACT
roots = list(root_orbit())
def act(word, v):
    for g in reversed(word): v = ACT[g](v)
    return v
def minus_roots(word):
    return sum(1 for r in roots if act(word, r) == tuple(-a for a in r))
cands = {
 'HH0 (K x I)': ['HH0'],
 'X0': ['X0'], 'Z0': ['HH0', 'X0', 'HH0'],
 'X0 X1': ['X0', 'X1'],
 'CX0': ['CX0'], 'CCX0': ['CCX0'],
 'HH0 X2': ['HH0', 'X2'],
 'HH0 HH1': ['HH0', 'HH1'],
 'X0 X1 X2': ['X0', 'X1', 'X2'],
 'CX0 X2': ['CX0', 'X2'],
}
for k, w in cands.items():
    print(f'{k:14s} roots in -1 eigenspace: {minus_roots(w)}')
