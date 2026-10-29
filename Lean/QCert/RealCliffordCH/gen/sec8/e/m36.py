"""Rules (36), (37): the decoded swaps and negations of A.4.1, checked numerically.

* D(E_{k,l}(swap)) (Lean `encSwap n k l`) is the swap of the wires l, l + 1: the decoded CZ,
  and by Lemma 8.5 and (354) the ZX on l controlled by l + 1, the XZ on l + 1 controlled by l
  and the ZX again (operator order CZ ZX XZ ZX; drawn ZX, XZ, ZX, CZ);
* D(E^0_{j,n-j-1}(X)) (Lean `encNeg n j (n-j-1) 0`) is X on the wire n - j - 1: Z there and the
  single-qubit ZX;
* the decoded right-hand sides of (36), (37) equal the decoded left-hand sides (semantics).
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import mc
import decode as dc

def gInv(n, s):
    acc = 0
    for i in range(n): acc ^= (s >> i)
    return acc
def gx(n, s): return gInv(n, s) % (2 ** n)
def grid(k, j): return [(x, y) for x in range(2 ** k) for y in range(2 ** j)]
def enc1Z(n, k, l):
    if l == 0:
        v = lambda t, x, b: t * 2 ** k + x * 2 + b
        return [('zz', gx(n, v(0, x, 1)), gx(n, v(1, x, 1))) for x in range(2 ** (k - 1))]
    l1 = l - 1
    v = lambda x, a, b, y: x * 2 ** (l1 + 2) + a * 2 ** (l1 + 1) + b * 2 ** l1 + y
    return [('zz', gx(n, v(p[0], 1, 0, p[1])), gx(n, v(p[0], 1, 1, p[1]))) for p in grid(k, l1)]
def enc2CZ(n, k, l):
    if l == 0:
        v = lambda t, x, a, b: t * 2 ** (k + 1) + x * 4 + a * 2 + b
        return [('zz', gx(n, v(0, x, 1, 1)), gx(n, v(1, x, 1, 1))) for x in range(2 ** (k - 1))]
    l1 = l - 1
    v = lambda x, a, b, y: x * 2 ** (l1 + 3) + 2 ** (l1 + 2) + a * 2 ** (l1 + 1) + b * 2 ** l1 + y
    return [('zz', gx(n, v(p[0], 1, 0, p[1])), gx(n, v(p[0], 1, 1, p[1]))) for p in grid(k, l1)]
def encSwap(n, k, l):
    v = lambda x, a, b, y: x * 2 ** (l + 2) + a * 2 ** (l + 1) + b * 2 ** l + y
    G = grid(k, l)
    A = [('zx', gx(n, v(x, 1, 1, y)), gx(n, v(x, 1, 0, y)), gx(n, v(x, 1, 1, y))) for x, y in G]
    B = [('zx', gx(n, v(x, 0, 1, y)), gx(n, v(x, 0, 1, y)), gx(n, v(x, 1, 1, y))) for x, y in G]
    return enc2CZ(n, k, l) + A + B + A
def encNeg(n, k, l, x0):
    if x0 == 1: return []
    v = lambda x, a, y: x * 2 ** (l + 1) + a * 2 ** l + y
    return enc1Z(n, k, l) + [('zx', gx(n, v(x, 1, y)), gx(n, v(x, 0, y)), gx(n, v(x, 1, y)))
                            for x, y in grid(k, l)]
def bitOf(v, i): return (v >> i) % 2
def restBit(n, ga, u, w, j):
    p, q = n - 1 - u, n - 1 - w
    i = j if j < p else (j + 1 if j + 1 < q else j + 2)
    return bitOf(ga, n - 1 - i)
def wW(n, kind, ga, u, w):
    l, m = u - w - 1, w
    sw = lambda k, j: encSwap(n, k, j)
    neg = lambda j: encNeg(n, j, n - j - 1, 1 - restBit(n, ga, u, w, j))
    mid = sw(n - 2, 0) if kind == 1 else []
    out = []
    for i in reversed(range(l)): out += sw(n - (m + 1 + i) - 2, m + 1 + i)
    for j in reversed(range(m)): out += sw(n - j - 2, j) + sw(n - j - 3, j + 1)
    out += mid
    for j in reversed(range(n - 2)): out += neg(j)
    out += [('hh', 0, 1, 3, 2)]
    for j in range(n - 2): out += neg(j)
    out += mid
    for j in range(m): out += sw(n - j - 3, j + 1) + sw(n - j - 2, j)
    for i in range(l): out += sw(n - (m + 1 + i) - 2, m + 1 + i)
    return out
def M(n, c): return mc.mat(n, c)
def D(n, w): return M(n, dc.decW(n, w))

bad = tot = 0
for n in [3, 4, 5]:
    for l in range(n - 1):
        k = n - l - 2
        tot += 1
        if not np.allclose(D(n, encSwap(n, k, l)), M(n, mc.swAt(n, l))): bad += 1; print('swap FAIL', n, l)
        v = lambda x, a, b, y: x * 2 ** (l + 2) + a * 2 ** (l + 1) + b * 2 ** l + y
        G = grid(k, l)
        A = [('zx', gx(n, v(x, 1, 1, y)), gx(n, v(x, 1, 0, y)), gx(n, v(x, 1, 1, y))) for x, y in G]
        B = [('zx', gx(n, v(x, 0, 1, y)), gx(n, v(x, 0, 1, y)), gx(n, v(x, 1, 1, y))) for x, y in G]
        ZXc = mc.mc(n, 'zx', [l], lambda j: True if j == l + 1 else None)
        XZc = mc.mc(n, 'xz', [l + 1], lambda j: True if j == l else None)
        tot += 2
        if not np.allclose(D(n, A), M(n, ZXc)): bad += 1; print('ZX merge FAIL', n, l)
        if not np.allclose(D(n, B), M(n, XZc)): bad += 1; print('XZ merge FAIL', n, l)
    for j in range(n):
        tot += 1
        if not np.allclose(D(n, encNeg(n, j, n - j - 1, 0)), M(n, mc.xAt(n, n - j - 1))):
            bad += 1; print('neg FAIL', n, j)
    for u in range(n):
        for w in range(u):
            for st in range(2 ** n):
                if (st >> u) & 1 or (st >> w) & 1: continue
                for kind in [1, 2]:
                    bu, bw = 1 << u, 1 << w
                    sts = [st, st | bu, st | bw, st | bu | bw] if kind == 1 else [st, st | bw, st | bu, st | bu | bw]
                    a, b, c, d = [gInv(n, q) for q in sts]
                    pt = dc.patt(n, a, b, c, d)
                    tot += 1
                    if pt != (kind, u, w): bad += 1; print('patt FAIL', n, a, b, c, d, pt); continue
                    if n == 5 and st % 3: continue
                    tot += 1
                    if not np.allclose(D(n, wW(n, kind, dc.gray(a), u, w)), D(n, [('hh', a, b, c, d)])):
                        bad += 1; print('rule FAIL', n, a, b, c, d, pt)
# the two-wire identity: drawn ZX(0|1), XZ(1|0), ZX(0|1), CZ = swap
c2 = mc.drawn(mc.mc(2, 'zx', [0], lambda j: True if j == 1 else None),
              mc.mc(2, 'xz', [1], lambda j: True if j == 0 else None),
              mc.mc(2, 'zx', [0], lambda j: True if j == 1 else None), mc.cz)
tot += 1
if not np.allclose(M(2, c2), M(2, mc.swap)): bad += 1; print('two-wire FAIL')
print('checked', tot, 'bad', bad)
