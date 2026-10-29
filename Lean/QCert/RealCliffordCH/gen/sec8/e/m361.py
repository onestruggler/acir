"""(361) through (359): the route of `D/N15/E361.lean`.

D(X03 X12) = [R, B1, B0, X0w, X0b, R, Z0b, Z0w] (drawn), with R = XZ[1](0 black),
B1 = box[1](0 black), B0 = box[0](1 black), X0w/X0b = XZ[0](1 white/black),
Z0b/Z0w the ZX, every other control white.  The single-qubit XZ on wire 0 is
the product over every colouring of the wires 1, ... (mergeListZ order):
x = Px * X0b * X0w (monoid), each factor of Px commuting with R ((352)),
z x = 1, and z R x = R2 = XZ[1](0 white) ((359) under the swap of wires 0, 1).
"""
import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
sys.path.insert(0, __import__('os').path.dirname(__file__))
from mc import *
import decode as dc
import numpy as np
def ctlOf(s, t): return lambda j: None if j == t else bool((s >> j) & 1)
def M(N, c): return mat(N, c)
def D(*ms):
    R = np.eye(ms[0].shape[0])
    for m in ms: R = m @ R
    return R
for N in [3, 4, 5]:
    I = np.eye(2 ** N)
    R = M(N, mc(N, 'xz', [1], ctlOf(1, 1))); B1 = M(N, mc(N, 'box', [1], ctlOf(1, 1)))
    B0 = M(N, mc(N, 'box', [0], ctlOf(3, 0)))
    X0w = M(N, mc(N, 'xz', [0], ctlOf(0, 0))); X0b = M(N, mc(N, 'xz', [0], ctlOf(3, 0)))
    Z0w = M(N, mc(N, 'zx', [0], ctlOf(0, 0))); Z0b = M(N, mc(N, 'zx', [0], ctlOf(3, 0)))
    R2 = M(N, mc(N, 'xz', [1], ctlOf(0, 1)))
    lhs = M(N, dc.dec(N, dc.Xx(0, 3, 1, 2))) if hasattr(dc, 'dec') else None
    word = D(R, B1, B0, X0w, X0b, R, Z0b, Z0w)
    ws = list(range(1, N))
    fs = []
    for i in range(2 ** len(ws)):
        c = {w: bool((i >> k) & 1) for k, w in enumerate(ws)}
        fs.append(M(N, mc(N, 'xz', [0], lambda j, c=c: c.get(j))))
    x = M(N, placeG(N, xz(0), [0])); z = M(N, placeG(N, zx(0), [0]))
    Px = D(*fs[2:]) if len(fs) > 2 else I
    rhs = D(B0, M(N, mc(N, 'xz', [1], colOn(2, N, lambda j: False))))
    print(N, 'dec', None if lhs is None else np.allclose(lhs, word),
          'merge', np.allclose(D(*fs), x), np.allclose(x, Px @ X0b @ X0w),
          'Px R', all(np.allclose(f @ R, R @ f) for f in fs[2:]),
          'zx', np.allclose(z @ x, I), '359', np.allclose(z @ R @ x, R2),
          'rot', np.allclose(R @ R, B1), np.allclose(B1 @ B1, I), np.allclose(B0 @ R @ B0, np.linalg.inv(R)),
          'merge R', np.allclose(R2 @ R, M(N, mc(N, 'xz', [1], colOn(2, N, lambda j: False)))),
          '361', np.allclose(word, rhs))
