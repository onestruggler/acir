"""Model of the Lean definitions of Syntax.lean / Sec8/MC.lean.

A circuit is a list of primitive gates in drawn order (first applied first):
('H', j), ('Z', j): on wire j;  ('CZ', j): wires j, j+1;  ('CH', j): H on wire j,
control on wire j+1.  Wire 0 is the least significant bit of a basis index.
"""
import numpy as np
from functools import lru_cache

s2 = 1 / np.sqrt(2)
Hm = np.array([[s2, s2], [s2, -s2]]); Zm = np.diag([1., -1.]); Xm = np.array([[0., 1], [1, 0]])
CZm = np.diag([1., 1, 1, -1])
# CH: control upper wire (bit 1 of the 2-wire index), H on lower (bit 0)
CHm = np.eye(4); CHm[2:, 2:] = Hm

def gate_matrix(N, g):
    kind, j = g
    if kind in ('H', 'Z'):
        A, k = (Hm if kind == 'H' else Zm), 1
    else:
        A, k = (CZm if kind == 'CZ' else CHm), 2
    assert j + k <= N, (g, N)
    # operator on wires j..j+k-1: index bits
    M = np.zeros((2 ** N, 2 ** N))
    mask = (2 ** k - 1) << j
    for col in range(2 ** N):
        sub = (col >> j) & (2 ** k - 1)
        rest = col & ~mask
        for r in range(2 ** k):
            v = A[r, sub]
            if v != 0:
                M[rest | (r << j), col] += v
    return M

def mat(N, c):
    M = np.eye(2 ** N)
    for g in c:
        M = gate_matrix(N, g) @ M
    return M

def shift(c, k=1): return [(g, j + k) for g, j in c]
def drawn(*cs):
    out = []
    for c in cs: out += c
    return out

h = [('H', 0)]; z = [('Z', 0)]; cz = [('CZ', 0)]; ch = [('CH', 0)]
x = drawn(h, z, h)
zw = drawn(x, z, x)
swap = drawn(cz, shift(h), h, cz, shift(h), h, cz, shift(h), h)
def conj(u, w): return drawn(u, w, u)
tau02 = drawn(swap, shift(swap), swap)
pp = drawn(ch, shift(h), z, ch, shift(h), z, ch, shift(h), z, swap)
zx2 = drawn(ch, conj(swap, shift(cz)), ch, conj(swap, shift(cz)))
xz2 = drawn(conj(swap, shift(cz)), ch, conj(swap, shift(cz)), ch)

@lru_cache(None)
def box_t(k):
    if k == 0: return tuple(drawn(z, zw))
    if k == 1: return tuple(shift(z))
    if k == 2: return tuple(shift(cz))
    B = conj(tau02, shift(list(box_t(k - 1))))
    return tuple(drawn(zx2, B, xz2, B))
def box(k): return list(box_t(k))
def zx(m):
    if m == 0: return drawn(x, z)
    return drawn(ch, conj(swap, box(m)), ch, conj(swap, box(m)))
def xz(m):
    if m == 0: return drawn(z, x)
    return drawn(conj(swap, box(m)), ch, conj(swap, box(m)), ch)
def mch(k):
    if k == 0: return shift(h)
    if k == 1: return shift(ch)
    return drawn(pp, box(k + 1), pp)

# ---- Sec8/Decoding + MC ----
def swAt(N, j): return shift(swap, j)
def xAt(N, j): return shift(x, j)
def moveDown(N, p, i): return [swAt(N, i + d) for d in reversed(range(p - i))]
def curPos(ps, i, q): return q + len([p for p in ps[:i] if q < p])
def netL(N, ps):
    out = []
    for i in range(len(ps)):
        out += moveDown(N, curPos(ps, i, ps[i]), i)
    return out
def placeG(N, g, ps):
    net = netL(N, ps)
    return drawn(*net, g, *reversed(net))
def colourW(N, ws, g):
    xs = [xAt(N, j) for j in ws]
    return drawn(*xs, g, *xs)
def ctrlWires(N, tg, c): return [j for j in range(N) if c(j) is not None and j not in tg]
def whiteWires(N, tg, c): return [j for j in range(N) if c(j) is False and j not in tg]
CANON = {'box': box, 'zx': zx, 'xz': xz, 'hg': mch}
def mc(N, K, tg, c):
    cs = ctrlWires(N, tg, c)
    return colourW(N, whiteWires(N, tg, c), placeG(N, CANON[K](len(cs)), tg + cs))
def blackOn(lo, hi): return lambda j: True if lo <= j < hi else None
def colOn(lo, hi, xf): return lambda j: bool(xf(j)) if lo <= j < hi else None
def ctlOr(c, d): return lambda j: c(j) if c(j) is not None else d(j)
def ctlAt(j0, b): return lambda j: b if j == j0 else None
def ctlDict(d): return lambda j: d.get(j)
def zAt(N, j): return placeG(N, z, [j])
def hAt(N, j): return placeG(N, h, [j])
def czAt(N, i, j): return placeG(N, cz, [i, j])
def chAt(N, t, c): return placeG(N, ch, [t, c])
def ppAt(N, i, j): return placeG(N, pp, [i, j])

# ---- intended semantics of mc ----
ZXm = Zm @ Xm; XZm = Xm @ Zm
def mc_sem(N, K, tg, c):
    M = np.eye(2 ** N)
    ctl = {j: c(j) for j in range(N) if c(j) is not None and j not in tg}
    def on(i): return all(((i >> j) & 1) == (1 if b else 0) for j, b in ctl.items())
    if K == 'box':
        for i in range(2 ** N):
            if on(i): M[i, i] = -1
        return M
    if K in ('zx', 'xz'):
        A = ZXm if K == 'zx' else XZm
        t = tg[0]
        M = np.zeros((2 ** N, 2 ** N))
        for col in range(2 ** N):
            if on(col):
                b = (col >> t) & 1
                for r in range(2):
                    M[(col & ~(1 << t)) | (r << t), col] += A[r, b]
            else:
                M[col, col] = 1
        return M
    if K == 'hg':
        hw = tg[1]
        M = np.zeros((2 ** N, 2 ** N))
        for col in range(2 ** N):
            if on(col):
                b = (col >> hw) & 1
                for r in range(2):
                    M[(col & ~(1 << hw)) | (r << hw), col] += Hm[r, b]
            else:
                M[col, col] = 1
        return M

def eq(N, a, b): return np.allclose(mat(N, a), mat(N, b))

if __name__ == '__main__':
    import itertools, random
    random.seed(1)
    bad = 0; tot = 0
    for N in range(2, 7):
        for K in ['box', 'zx', 'xz', 'hg']:
            for _ in range(25):
                ntg = 2 if K == 'hg' else 1
                if N < ntg + (0 if K != 'hg' else 0): continue
                tg = random.sample(range(N), ntg)
                d = {}
                for j in range(N):
                    if j in tg: continue
                    r = random.random()
                    d[j] = None if r < 0.25 else (r < 0.6)
                c = ctlDict(d)
                ok = np.allclose(mat(N, mc(N, K, tg, c)), mc_sem(N, K, tg, c))
                tot += 1
                if not ok:
                    bad += 1; print('MISMATCH', N, K, tg, d)
    print('checked', tot, 'bad', bad)
