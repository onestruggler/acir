"""Rule (45): the decoded letters (for the next step; no Lean proof yet).

D(H_[0,1]H_[7,6]) = E1 = hg[2,0](1 white, 3.. white)   (H on wire 0, box wire 2)
D(H_[0,3]H_[1,2]) = E2 = hg[0,1](2.. white)             (H on wire 1, box wire 0)
D((-1)_[0](-1)_[1]) = Bw = box[0](1.. white)
Rule (45) decoded (monoid order) is E1 E2 E1 Bw E2 = E2 Bw E1 E2 E1, i.e. (146)
`ΛH(1|2○) · CZ(2○,1○) · ΛH(0|1○) · ΛH(1|2○) · ΛH(0|1○) = ...` (drawn order) with
every wire above 2 a white control.
"""
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
sys.path.insert(0, __import__('os').path.dirname(__file__))
from mc import *
import decode as dc
import numpy as np
def M(N, c): return mat(N, c)
for N in [3, 4, 5]:
    w = lambda lo: colOn(lo, N, lambda j: False)
    E1 = M(N, mc(N, 'hg', [2, 0], ctlOr(ctlAt(1, False), w(3))))
    E2 = M(N, mc(N, 'hg', [0, 1], w(2)))
    Bw = M(N, mc(N, 'box', [0], w(1)))
    d = lambda p: M(N, dc.dec(N, p))
    print(N, 'E1', np.allclose(d(dc.Hh(0, 1, 7, 6)), E1), 'E2', np.allclose(d(dc.Hh(0, 3, 1, 2)), E2),
          'Bw', np.allclose(d(dc.Zz(0, 1)), Bw),
          'rule', np.allclose(E1 @ E2 @ E1 @ Bw @ E2, E2 @ Bw @ E1 @ E2 @ E1))
