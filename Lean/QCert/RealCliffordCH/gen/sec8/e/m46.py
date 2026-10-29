"""Rule (46): the decoded letters (`E/Rule46.lean`).

D(H_[0,1]H_[7,6]) = A  = hg[2,0](1 white, 3.. white)   (H on wire 0, box wire 2)
D(H_[0,3]H_[1,2]) = B  = hg[0,1](2.. white)             (H on wire 1, box wire 0)
D(H_[3,4]H_[2,5]) = Cc = hg[0,2](1 black, 3.. white)    (H on wire 2, box wire 0)
D(H_[3,2]H_[4,5]) = Dd = hg[2,0](1 black, 3.. white)    (H on wire 0, box wire 2)
D(H_[7,6]H_[4,5]) = F  = hg[1,0](2 black, 3.. white)    (H on wire 0, box wire 1)
D((-1)_[2](-1)_[3]) = Z = box[0](1 black, 2 white, 3.. white)
Rule (46) decoded (monoid order): A B Cc Dd F Z Cc B = B Cc Z F Dd Cc B A, i.e. (147)
with every wire above 2 a white control.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mc import *
import decode as dc
import numpy as np
def M(N, c): return mat(N, c)
for N in [3, 4, 5]:
    w = lambda lo: colOn(lo, N, lambda j: False)
    A = M(N, mc(N, 'hg', [2, 0], ctlOr(ctlAt(1, False), w(3))))
    B = M(N, mc(N, 'hg', [0, 1], w(2)))
    Cc = M(N, mc(N, 'hg', [0, 2], ctlOr(ctlAt(1, True), w(3))))
    Dd = M(N, mc(N, 'hg', [2, 0], ctlOr(ctlAt(1, True), w(3))))
    F = M(N, mc(N, 'hg', [1, 0], ctlOr(ctlAt(2, True), w(3))))
    Z = M(N, mc(N, 'box', [0], ctlOr(ctlAt(1, True), ctlOr(ctlAt(2, False), w(3)))))
    d = lambda p: M(N, dc.dec(N, p))
    ok = [np.allclose(d(dc.Hh(0, 1, 7, 6)), A), np.allclose(d(dc.Hh(0, 3, 1, 2)), B),
          np.allclose(d(dc.Hh(3, 4, 2, 5)), Cc), np.allclose(d(dc.Hh(3, 2, 4, 5)), Dd),
          np.allclose(d(dc.Hh(7, 6, 4, 5)), F), np.allclose(d(dc.Zz(2, 3)), Z)]
    # monoid order: product left to right = matrix product left to right
    L = A @ B @ Cc @ Dd @ F @ Z @ Cc @ B
    R = B @ Cc @ Z @ F @ Dd @ Cc @ B @ A
    lhs = [dc.Hh(0,1,7,6), dc.Hh(0,3,1,2), dc.Hh(3,4,2,5), dc.Hh(3,2,4,5), dc.Hh(7,6,4,5), dc.Zz(2,3), dc.Hh(3,4,2,5), dc.Hh(0,3,1,2)]
    rhs = [dc.Hh(0,3,1,2), dc.Hh(3,4,2,5), dc.Zz(2,3), dc.Hh(7,6,4,5), dc.Hh(3,2,4,5), dc.Hh(3,4,2,5), dc.Hh(0,3,1,2), dc.Hh(0,1,7,6)]
    print(N, ok, 'rule', np.allclose(L, R), 'decW', np.allclose(M(N, dc.decW(N, lhs)), L), np.allclose(M(N, dc.decW(N, rhs)), R))
