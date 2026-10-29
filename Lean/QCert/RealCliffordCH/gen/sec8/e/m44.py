"""Rule (44): the route of `E/Rule44.lean`.

D(X03 X12) = Xi Bw (361) and the gadget G = hg[1,0] (white above) commute:
Bw by (338); Xi, all controls black first: hg[0,1] = P Bx P (Definition 2.4,
on three wires (18)), the swap of the wires 0, 1 fixes P ((112)), so
G = P Bq P with Bq = box[1](0 black); P Xi P = Zi (360); Zi = Zi(0 black)
Zi(0 white) ((354)), each commuting with Bq ((346) under the swap).
Then X on the wires 2, ... colours everything white.
"""
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
sys.path.insert(0, __import__('os').path.dirname(__file__))
from mc import *
import decode as dc
import numpy as np
def M(N, c): return mat(N, c)
W = lambda N: colOn(2, N, lambda j: False)
for N in [3, 4, 5]:
    P = M(N, ppAt(N, 0, 1)); S = M(N, swAt(N, 0))
    Bx = M(N, mc(N, 'box', [0], blackOn(1, N)))
    Hb = M(N, mc(N, 'hg', [0, 1], blackOn(2, N)))
    Gb = M(N, mc(N, 'hg', [1, 0], blackOn(2, N)))
    Bq = M(N, mc(N, 'box', [1], ctlOr(ctlAt(0, True), blackOn(2, N))))
    Xb = M(N, mc(N, 'xz', [1], blackOn(2, N))); Zb = M(N, mc(N, 'zx', [1], blackOn(2, N)))
    Z0b = M(N, mc(N, 'zx', [1], ctlOr(ctlAt(0, True), blackOn(2, N))))
    Z0w = M(N, mc(N, 'zx', [1], ctlOr(ctlAt(0, False), blackOn(2, N))))
    G = M(N, mc(N, 'hg', [1, 0], W(N))); Xi = M(N, mc(N, 'xz', [1], W(N)))
    Bw = M(N, mc(N, 'box', [0], ctlOr(ctlAt(1, True), W(N))))
    DX = M(N, dc.dec(N, dc.Xx(0, 3, 1, 2)))
    print(N, 'hgPP', np.allclose(Hb, P @ Bx @ P), 'SPS', np.allclose(S @ P @ S, P),
          'SHS', np.allclose(S @ Hb @ S, Gb), 'SBS', np.allclose(S @ Bx @ S, Bq),
          '360', np.allclose(P @ Xb @ P, Zb), 'split', np.allclose(Zb, Z0w @ Z0b),
          'comm', np.allclose(Z0b @ Bq, Bq @ Z0b), np.allclose(Z0w @ Bq, Bq @ Z0w),
          'black', np.allclose(Xb @ Gb, Gb @ Xb), 'white', np.allclose(Xi @ G, G @ Xi),
          '338', np.allclose(Bw @ G, G @ Bw), '361', np.allclose(DX, Xi @ Bw),
          'rule44', np.allclose(DX @ G, G @ DX))
