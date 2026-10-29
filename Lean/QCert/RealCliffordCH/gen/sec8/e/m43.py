"""Rule (43): the route of `E/Rule43.lean` (the paper's chain in the frame of
P = P (x) P on the wires 0, 1, then Y = Xi B0 = B0 Zi).  Monoid order is matrix order.

G  = hg[1,0](2..w)        (the gadget)         A   = hg[2,0](1b, 3..w) = D(H32 H45)
Bg = box[1](0b, 2..w)                          A'' = hg[2,1](0b, 3..w)
B0 = box[0](1b, 2..w)     B2 = box[2](0b, 1b, 3..w)
R/Ri = XZ/ZX[1](0b, 2..w)   Xiw/Riw = XZ/ZX[1](0w, 2..w)   Xi/Zi = XZ/ZX[1](2..w)
"""
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
sys.path.insert(0, __import__('os').path.dirname(__file__))
from mc import *
import decode as dc
import numpy as np
def M(N, c): return mat(N, c)
def ok(a, b): return np.allclose(a, b)
for N in [3, 4, 5]:
    w2 = colOn(2, N, lambda j: False); w3 = colOn(3, N, lambda j: False)
    G = M(N, mc(N, 'hg', [1, 0], w2)); A = M(N, mc(N, 'hg', [2, 0], ctlOr(ctlAt(1, True), w3)))
    Bg = M(N, mc(N, 'box', [1], ctlOr(ctlAt(0, True), w2)))
    A2 = M(N, mc(N, 'hg', [2, 1], ctlOr(ctlAt(0, True), w3)))
    B0 = M(N, mc(N, 'box', [0], ctlOr(ctlAt(1, True), w2)))
    B2 = M(N, mc(N, 'box', [2], ctlOr(ctlAt(0, True), ctlOr(ctlAt(1, True), w3))))
    R = M(N, mc(N, 'xz', [1], ctlOr(ctlAt(0, True), w2))); Ri = M(N, mc(N, 'zx', [1], ctlOr(ctlAt(0, True), w2)))
    Xiw = M(N, mc(N, 'xz', [1], ctlOr(ctlAt(0, False), w2))); Riw = M(N, mc(N, 'zx', [1], ctlOr(ctlAt(0, False), w2)))
    Xi = M(N, mc(N, 'xz', [1], w2)); Zi = M(N, mc(N, 'zx', [1], w2))
    P = M(N, ppAt(N, 0, 1)); P02 = M(N, ppAt(N, 0, 2)); P20 = M(N, ppAt(N, 2, 0))
    P12 = M(N, ppAt(N, 1, 2)); P21 = M(N, ppAt(N, 2, 1))
    DH = M(N, dc.dec(N, dc.Hh(3, 2, 4, 5))); DX = M(N, dc.dec(N, dc.Xx(0, 3, 1, 2)))
    I = np.eye(2 ** N)
    print(N, 'dec', ok(DH, A), ok(DX, Xi @ B0), 'G', ok(G, P @ Bg @ P),
          'A', ok(A, P20 @ B2 @ P20), ok(A2, P21 @ B2 @ P21), ok(P20, P02), ok(P21, P12),
          'klein', ok(P @ P02 @ P, P12), ok(P @ P02, P12), 'PAP', ok(P @ A @ P, A2),
          'RR', ok(R @ R, Bg), 'RA', ok(R @ A2, A2 @ Ri), 'comm', ok(A2 @ Riw, Riw @ A2),
          'mrg', ok(R @ Xiw, Xi), ok(Riw @ Ri, Zi), 'inv', ok(Xiw @ Riw, I),
          '360', ok(P @ Xi @ P, Zi), ok(P @ Zi @ P, Xi),
          'B0', ok(B0 @ A, A @ B0), ok(B0 @ G, G @ B0), ok(B0 @ Riw @ B0, Xiw), ok(B0 @ Ri @ B0, R),
          'rule', ok(G @ A, DX @ A @ DX))
