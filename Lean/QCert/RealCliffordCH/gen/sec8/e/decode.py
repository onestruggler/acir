"""Model of Sec8/Encoding.lean, Sec8/Fig8.lean and Sec8/Decoding.lean (package (vi)).

Circuits are gate lists of ../mc.py (drawn order).  Every function mirrors the Lean
definition of the same name, so that the decoded letters are the Lean circuits on the nose.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import numpy as np
import mc
from mc import drawn

def gray(k): return k ^ (k >> 1)
def gInv(n, s):
    acc = 0
    for i in range(n): acc ^= (s >> i)
    return acc
def bitOf(v, i): return (v >> i) % 2

# ---- Fig8.lean
def tau(e, k, i, v):
    if e == 0: return v
    if v == k: return i
    if v == i: return k
    return v
def Zz(a, c): return ('zz', a, c)
def Zx(a, c, d): return ('zx', a, c, d)
def Xx(a, b, c, d): return ('xx', a, b, c, d)
def Hh(a, b, c, d): return ('hh', a, b, c, d)
def sigmaW(a, b, c, d):
    e3 = 1 if d != 2 else 0
    m3 = tau(e3, d, 2, 4); i2 = tau(e3, d, 2, 3)
    e2 = 1 if c != i2 else 0
    m2 = tau(e2, c, i2, tau(e3, d, 2, 4)); i1 = tau(e2, c, i2, tau(e3, d, 2, 1))
    e1 = 1 if b != i1 else 0
    m1 = tau(e1, b, i1, tau(e2, c, i2, tau(e3, d, 2, 4)))
    i0 = tau(e1, b, i1, tau(e2, c, i2, tau(e3, d, 2, 0)))
    e0 = 1 if a != i0 else 0
    m0 = tau(e0, a, i0, tau(e1, b, i1, tau(e2, c, i2, tau(e3, d, 2, 4))))
    L = lambda e, m, k, i: [Zx(m, k, i)] if e == 1 else []
    return (L(e0, m0, a, i0) + L(e1, m1, b, i1) + L(e2, m2, c, i2) + L(e3, m3, d, 2),
            L(e3, 4, d, 2) + L(e2, m3, c, i2) + L(e1, m2, b, i1) + L(e0, m1, a, i0))
def clear2(v, u, w): return v - bitOf(v, u) * 2 ** u - bitOf(v, w) * 2 ** w
def patt(n, a, b, c, d):
    g = gray
    for u in range(n):
        for w in range(u):
            same = clear2(g(a), u, w) == clear2(g(b), u, w) == clear2(g(c), u, w) == clear2(g(d), u, w)
            bits = lambda t: (bitOf(g(t), u), bitOf(g(t), w))
            if same and bits(a) == (0, 0) and bits(b) == (1, 0) and bits(c) == (0, 1) and bits(d) == (1, 1):
                return (1, u, w)
            if same and bits(a) == (0, 0) and bits(b) == (0, 1) and bits(c) == (1, 0) and bits(d) == (1, 1):
                return (2, u, w)
    return None
def freshPair(n, a, b, c, d):
    l = [e for e in range(2 ** n) if e not in (a, b, c, d)]
    return (l[0], l[1]) if len(l) >= 2 else (0, 0)
def Distinct4(a, b, c, d): return len({a, b, c, d}) == 4

# ---- Decoding.lean
def swAt(n, j): return mc.swAt(n, j)
def xAt(n, j): return mc.xAt(n, j)
def down(n, t): return [swAt(n, j) for j in reversed(range(t))]
def down1(n, h): return [swAt(n, j) for j in reversed(range(h)) if j >= 1]
def stdBox(N): return mc.box(N - 1) if N >= 1 else []
def stdZX(N): return mc.zx(N - 1) if N >= 1 else []
def stdXZ(N): return mc.xz(N - 1) if N >= 1 else []
def stdMch(N): return mc.mch(N - 2) if N >= 2 else []
def placeAt(n, g, t):
    d = down(n, t); return drawn(*d, g, *reversed(d))
def placeAt2(n, g, h, b):
    h1 = h + 1 if h < b else h
    net = down(n, b) + down1(n, h1)
    return drawn(*net, g, *reversed(net))
def colour(n, g, colours, skip):
    xs = [xAt(n, j) for j in range(n) if not skip(j) and colours(j) == 0]
    return drawn(*xs, g, *xs)
def tOf(n, a):
    ga = gray(a)
    for j in range(n):
        if bitOf(ga, j) != bitOf(gray(a + 1), j): return j
    return 0
def dZZ1(n, a):
    t = tOf(n, a); ga = gray(a)
    return colour(n, placeAt(n, stdBox(n), t), lambda j: bitOf(ga, j), lambda j: j == t)
def dZX1(n, a, which):
    t = tOf(n, a); ga = gray(a); beta = bitOf(ga, t)
    g = stdXZ(n) if (which == 0) == (beta == 0) else stdZX(n)
    return colour(n, placeAt(n, g, t), lambda j: bitOf(ga, j), lambda j: j == t)
def dZZ(n, a, b):
    return drawn(*[dZZ1(n, min(a, b) + i) for i in range(max(a, b) - min(a, b))])
def dZXab(n, fuel, s, a, b):
    if fuel == 0: return []
    f = fuel - 1
    if b == a + 1: return dZX1(n, a, 0 if s == a else 1)
    if (b - a) % 2 == 1:
        if s == a: return drawn(dZX1(n, a, 0), dZXab(n, f, a + 1, a + 1, b), dZX1(n, a, 1))
        return drawn(dZX1(n, a, 0), dZXab(n, f, b, a + 1, b), dZX1(n, a, 1))
    if s == a: return drawn(dZX1(n, b - 1, 1), dZXab(n, f, a, a, b - 1), dZX1(n, b - 1, 0))
    return drawn(dZX1(n, b - 1, 1), dZXab(n, f, b - 1, a, b - 1), dZX1(n, b - 1, 0))
def dZX(n, c, a, b):
    lo, hi = min(a, b), max(a, b)
    if c == a or c == b: return dZXab(n, hi - lo, c, lo, hi)
    return drawn(dZXab(n, hi - lo, a, lo, hi), dZZ(n, c, a))
def dHH4(n, a, b, c, d):
    p = patt(n, a, b, c, d)
    if p is not None:
        kind, u, w = p
        h, bx = (u, w) if kind == 1 else (w, u)
        return colour(n, placeAt2(n, stdMch(n), h, bx), lambda j: bitOf(gray(a), j), lambda j: j == u or j == w)
    gadget = colour(n, placeAt2(n, stdMch(n), 0, 1), lambda j: 0, lambda j: j < 2)
    s1, s2 = sigmaW(a, b, c, d)
    dW = lambda l: drawn(*reversed([dZX(n, q[1], q[2], q[3]) if q[0] == 'zx' else [] for q in l]))
    return drawn(dW(s2), gadget, dW(s1))
def dec(n, p):
    t = p[0]
    if t == 'zz': return dZZ(n, p[1], p[2])
    if t == 'zx':
        _, a, c, d = p
        return [] if c == d else dZX(n, a, c, d)
    if t == 'xx':
        _, a, b, c, d = p
        return [] if a == b or c == d else drawn(dZX(n, b, c, d), dZX(n, a, a, b))
    _, a, b, c, d = p
    if a == b or c == d: return []
    if Distinct4(a, b, c, d): return dHH4(n, a, b, c, d)
    e, f = freshPair(n, a, b, c, d)
    return drawn(dHH4(n, e, f, c, d), dHH4(n, a, b, e, f))
def decW(n, w):
    # decW (p1 p2 ... pk) = dec p1 * ... * dec pk = drawn [dec pk, ..., dec p1]
    return drawn(*[dec(n, p) for p in reversed(w)])

# ---- semantics of letters in the Gray basis
s2 = 1 / np.sqrt(2)
def gneg(N, a): M = np.eye(N); M[a, a] = -1; return M
def gX(N, a, b): M = np.eye(N); M[a, a] = M[b, b] = 0; M[a, b] = M[b, a] = 1; return M
def gH(N, a, b): M = np.eye(N); M[a, a] = s2; M[a, b] = s2; M[b, a] = s2; M[b, b] = -s2; return M
def psem(N, p):
    t = p[0]
    if t == 'zz': return gneg(N, p[1]) @ gneg(N, p[2])
    if t == 'zx': return gneg(N, p[1]) @ gX(N, p[2], p[3])
    if t == 'xx': return gX(N, p[1], p[2]) @ gX(N, p[3], p[4])
    return gH(N, p[1], p[2]) @ gH(N, p[3], p[4])
def wsem(N, w):
    M = np.eye(N)
    for p in w: M = M @ psem(N, p)
    return M
def toP(n, M):
    idx = [gray(i) for i in range(2 ** n)]
    return M[np.ix_(idx, idx)]
import fast
def csemP(n, c): return toP(n, fast.mat(n, c))
