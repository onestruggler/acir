"""Engine letters (Sec8/EngineN.lean, `Eng.L`) for the circuits of Syntax.lean / Sec8/MC.lean.

A letter is a pair (kind, j): ('H', j), ('Z', j) on wire j; ('C', j) = CZ, ('K', j) = CH
(H on wire j, control on j + 1), ('S', j) = the swap, on wires j, j + 1.  Words are in
drawn order.  The functions mirror the Lean definitions exactly (same swap networks, same
recursions), so that `circW N (word)` is the Lean circuit on the nose.
"""
from functools import lru_cache

import numpy as np

import mc


def sh(w, k=1):
    return [(a, j + k) for a, j in w]


H0 = [('H', 0)]
Z0 = [('Z', 0)]
C0 = [('C', 0)]
K0 = [('K', 0)]
S0 = [('S', 0)]
X0 = H0 + Z0 + H0
ZW0 = X0 + Z0 + X0
PP0 = K0 + sh(H0) + Z0 + K0 + sh(H0) + Z0 + K0 + sh(H0) + Z0 + S0
TAU02 = S0 + sh(S0) + S0


def conj(u, w):
    return u + w + u


@lru_cache(None)
def _box(k):
    if k == 0:
        return tuple(Z0 + ZW0)
    if k == 1:
        return tuple(sh(Z0))
    if k == 2:
        return tuple(sh(C0))
    B = conj(TAU02, sh(list(_box(k - 1))))
    return tuple(zx(2) + B + xz(2) + B)


def box(k):
    return list(_box(k))


def zx(m):
    if m == 0:
        return X0 + Z0
    if m == 2:
        return K0 + conj(S0, sh(C0)) + K0 + conj(S0, sh(C0))
    return K0 + conj(S0, box(m)) + K0 + conj(S0, box(m))


def xz(m):
    if m == 0:
        return Z0 + X0
    if m == 2:
        return conj(S0, sh(C0)) + K0 + conj(S0, sh(C0)) + K0
    return conj(S0, box(m)) + K0 + conj(S0, box(m)) + K0


def mch(k):
    if k == 0:
        return sh(H0)
    if k == 1:
        return sh(K0)
    return PP0 + box(k + 1) + PP0


# ---- MC.lean
def swAt(j): return [('S', j)]
def xAt(j): return sh(X0, j)
def zAt(j): return [('Z', j)]
def hAt(j): return [('H', j)]


def moveDown(p, i): return [('S', i + d) for d in reversed(range(p - i))]
def curPos(ps, i, q): return q + len([p for p in ps[:i] if q < p])


def netL(ps):
    out = []
    for i in range(len(ps)):
        out += moveDown(curPos(ps, i, ps[i]), i)
    return out


def placeG(g, ps):
    net = netL(ps)
    return net + g + list(reversed(net))


def place(g, ps):
    """`g` (on its own len(ps) wires) with its wire i on wire ps[i]: shifted when ps is
    contiguous and increasing; a two-wire gate on wires lo < hi that are not adjacent is
    conjugated by the swaps carrying wire lo up to hi - 1 (as the paper's cz20, ch20), and
    one placed upside down by the swap of its two wires; otherwise MC's network (placeG)."""
    k = len(ps)
    if ps == list(range(ps[0], ps[0] + k)):
        return sh(g, ps[0])
    if k == 2:
        lo, hi = min(ps), max(ps)
        inner = sh(g, hi - 1)
        if ps[0] > ps[1]:
            inner = [('S', hi - 1)] + inner + [('S', hi - 1)]
        net = [('S', j) for j in range(lo, hi - 1)]
        return net + inner + list(reversed(net))
    return placeG(g, ps)


def colourW(ws, g):
    xs = [l for j in ws for l in xAt(j)]
    return xs + g + xs


CANON = {'box': box, 'zx': zx, 'xz': xz, 'hg': mch}


def mcw(N, K, tg, c):
    cs = [j for j in range(N) if c(j) is not None and j not in tg]
    ws = [j for j in range(N) if c(j) is False and j not in tg]
    return colourW(ws, place(CANON[K](len(cs)), tg + cs))


def czAt(i, j): return place(C0, [i, j])
def chAt(t, c): return place(K0, [t, c])
def ppAt(i, j): return place(PP0, [i, j])


# ---- semantics: letters to mc.py primitive gates
def prim(w):
    out = []
    for a, j in w:
        if a == 'H': out.append(('H', j))
        elif a == 'Z': out.append(('Z', j))
        elif a == 'C': out.append(('CZ', j))
        elif a == 'K': out.append(('CH', j))
        elif a == 'S': out += mc.shift(mc.swap, j)
    return out


def mat(N, w):
    return mc.mat(N, prim(w))


def eq(N, u, v):
    return np.allclose(mat(N, u), mat(N, v), atol=1e-9)


def lo(l): return l[1]
def wd(l): return 1 if l[0] in 'HZ' else 2
def wires(l): return set(range(l[1], l[1] + wd(l)))
def disj(x, y): return not (wires(x) & wires(y))


def lean(w):
    return '[' + ', '.join(f'L.{a} {j}' for a, j in w) + ']'
