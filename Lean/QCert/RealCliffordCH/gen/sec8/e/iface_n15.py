"""Numerical check of the statements (353)-(361) of Sec8/D/N15.lean, as transcribed in Lean,
at widths 2-6 (`python iface_n15.py`): every parameter value (colourings of up to 5 wires
exhaustively, else random)."""
import itertools, random
from decode import *
import fast
from mc import mc as MC, blackOn, colOn, ctlAt, ctlOr, swAt as SW, xAt as XA, czAt, ppAt, placeG, zx, xz
def setCtl(c, w, v): return lambda j: v if j == w else c(j)
def sgn(a): return 'xz' if a else 'zx'
def eqm(N, l, r): return np.allclose(fast.mat(N, l), fast.mat(N, r), atol=1e-9)
def cols(N, lo):
    for bits in itertools.product([False, True], repeat=N - lo):
        yield (lambda b: (lambda j: b[j - lo] if lo <= j < N else False))(bits)
res = {}
def rec(name, N, ok):
    res.setdefault(name, {}).setdefault(N, [0, 0])[0 if ok else 1] += 1
for N in range(2, 7):
    for a in (False, True):
        K = sgn(a)
        if N >= 3:
            for j in range(1, N - 1):
                g = MC(N, K, [0], blackOn(1, N))
                rec('353', N, eqm(N, drawn(g, SW(N, j)), drawn(SW(N, j), g)))
        for x in cols(N, 1):
            for w in range(1, N):
                for b in (False, True):
                    c = colOn(1, N, x)
                    l = drawn(MC(N, K, [0], setCtl(c, w, b)), MC(N, K, [0], setCtl(c, w, not b)))
                    rec('354', N, eqm(N, l, MC(N, K, [0], setCtl(c, w, None))))
                    for al in (False, True):
                        G = lambda v: MC(N, K, [0], setCtl(c, w, v))
                        xzw = placeG(N, xz(0), [w]); zxw = placeG(N, zx(0), [w])
                        rec('359a', N, eqm(N, drawn(xzw, G(al), zxw), G(not al)))
                        rec('359b', N, eqm(N, drawn(zxw, G(al), xzw), G(not al)))
            g = MC(N, K, [0], colOn(1, N, x))
            rec('355', N, eqm(N, drawn(g, g), MC(N, 'box', [0], colOn(1, N, x))))
    zx0 = MC(N, 'zx', [0], blackOn(1, N)); xz0 = MC(N, 'xz', [0], blackOn(1, N))
    rec('356', N, eqm(N, drawn(XA(N, 0), zx0, XA(N, 0)), xz0))
    rec('357', N, eqm(N, drawn(czAt(N, 0, 1), zx0, czAt(N, 0, 1)), xz0))
    if N >= 2:
        z1 = MC(N, 'zx', [1], ctlOr(ctlAt(0, True), blackOn(2, N)))
        rec('358', N, eqm(N, drawn(xz0, z1, xz0), drawn(z1, xz0, z1)))
        rec('360', N, eqm(N, drawn(ppAt(N, 0, 1), MC(N, 'zx', [1], blackOn(2, N))),
                           drawn(MC(N, 'xz', [1], blackOn(2, N)), ppAt(N, 0, 1))))
        rec('360swapped', N, eqm(N, drawn(ppAt(N, 1, 0), MC(N, 'zx', [1], blackOn(2, N))),
                           drawn(MC(N, 'xz', [1], blackOn(2, N)), ppAt(N, 1, 0))))
    if 3 <= N <= 5:
        white = colOn(2, N, lambda j: False)
        r = drawn(MC(N, 'box', [0], ctlOr(ctlAt(1, True), white)), MC(N, 'xz', [1], white))
        rec('361', N, eqm(N, decW(N, [Xx(0, 3, 1, 2)]), r))
for k in sorted(res): print(k, {N: tuple(v) for N, v in sorted(res[k].items())})
