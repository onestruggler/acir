"""(360) by (333)/(334) one width down: the route of `D/N15/E360.lean`.

a  = ZX on wire 1, controls 2.. black, wire 0 idle;  a' = the XZ.
H0 = hg[3,1](2, 4..),  B0 = box[2](1, 3..)        ((333) lifted past wire 0)
H1 = hg[0,1](2, 4..),  B1 = box[0](1, 3..)        (box wires moved by (277), (274))
H2 = hg[0,1](3..),     B2 = box[0](1, 2, 4..)     (P (x) P on wires 0, 1 exchanges them)
S  = the swap of the wires 2, 3.
Monoid order = matrix order (first applied last); `D(...)` is drawn order.
"""
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
from mc import *
import numpy as np
def M(N, c): return mat(N, c)
def D(*ms):
    R = np.eye(ms[0].shape[0])
    for m in ms: R = m @ R
    return R
for N in [4, 5, 6]:
    cH = ctlOr(ctlAt(2, True), blackOn(4, N)); cB = ctlOr(ctlAt(1, True), blackOn(3, N))
    a = M(N, mc(N, 'zx', [1], blackOn(2, N))); ai = M(N, mc(N, 'xz', [1], blackOn(2, N)))
    H0 = M(N, mc(N, 'hg', [3, 1], cH)); B0 = M(N, mc(N, 'box', [2], cB))
    H1 = M(N, mc(N, 'hg', [0, 1], cH)); B1 = M(N, mc(N, 'box', [0], cB))
    H2 = M(N, mc(N, 'hg', [0, 1], blackOn(3, N)))
    B2 = M(N, mc(N, 'box', [0], ctlOr(ctlAt(1, True), ctlOr(ctlAt(2, True), blackOn(4, N)))))
    P = M(N, ppAt(N, 0, 1)); S = M(N, swAt(N, 2))
    print(N, '333 lift', np.allclose(a, D(H0, B0, H0, B0)), '334 lift', np.allclose(ai, D(B0, H0, B0, H0)),
          'moves', np.allclose(H0, H1), np.allclose(B0, B1),
          'PHP', np.allclose(P @ H1 @ P, B2), 'PBP', np.allclose(P @ B1 @ P, H2),
          'S', np.allclose(S @ H1 @ S, H2), np.allclose(S @ B1 @ S, B2), np.allclose(S @ ai @ S, ai),
          '360', np.allclose(a @ P, P @ ai))
# the width-3 instance of `pp box pp = mch`
N = 3
print('pp box2 pp = mch1', np.allclose(M(3, drawn(pp, box(2), pp)), M(3, mch(1))))
