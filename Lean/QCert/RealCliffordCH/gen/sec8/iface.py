"""Numerical check of the interface statements of Sec8/D (as transcribed in Lean)."""
import sys, itertools, random
sys.path.insert(0, '.')
from mc import *

def setCtl(c, w, v): return lambda j: v if j == w else c(j)
def U(*cs):  # ctlOr chain
    def f(j):
        for c in cs:
            if c(j) is not None: return c(j)
        return None
    return f
def sgn(a): return 'xz' if a else 'zx'
def D(N, *gs): return drawn(*gs)

EQS = {}
def stmt(name):
    def deco(f): EQS[name] = f; return f
    return deco

B = lambda N: mc(N, 'box', [0], blackOn(1, N))

@stmt('274')
def _(N, r): return mc(N, 'box', [1], blackOn(2, N)), mc(N, 'box', [0], blackOn(2, N))
@stmt('277')
def _(N, r): return mc(N, 'hg', [1, 2], blackOn(3, N)), mc(N, 'hg', [0, 2], blackOn(3, N))
@stmt('299')
def _(N, r): return D(N, B(N), B(N)), []
@stmt('305')
def _(N, r):
    b1 = mc(N, 'box', [1], U(ctlAt(0, True), blackOn(2, N)))
    return D(N, mc(N, 'xz', [0], ctlAt(1, True)), b1, mc(N, 'zx', [0], ctlAt(1, True)), b1), B(N)
@stmt('307')
def _(N, r):
    if N < 3: return None
    j = r.randrange(1, N - 1)
    return D(N, B(N), swAt(N, j)), D(N, swAt(N, j), B(N))
@stmt('308')
def _(N, r):
    m = r.randrange(1, N + 1)
    C = [(r.choice(['H', 'Z', 'CZ', 'CH']), None) for _ in range(6)]
    C = [(g, r.randrange(0, m - (1 if g in ('H', 'Z') else 2) + 1)) for g, _ in C if m >= (1 if g in ('H', 'Z') else 2)]
    g = mc(N, 'box', [m - 1], blackOn(m, N))
    return D(N, C, g), D(N, g, C)
def rx(r):
    t = [r.random() < 0.5 for _ in range(12)]
    return lambda j: t[j]
@stmt('309')
def _(N, r):
    if N < 2: return None
    x = rx(r); w = r.randrange(1, N); b = r.random() < 0.5; c = colOn(1, N, x)
    g = lambda v: mc(N, 'box', [0], setCtl(c, w, v))
    return D(N, g(b), g(not b)), g(None)
@stmt('310')
def _(N, r):
    if N < 3: return None
    x = rx(r); w = r.randrange(2, N); b = r.random() < 0.5; c = colOn(2, N, x)
    g = lambda v: mc(N, 'hg', [0, 1], setCtl(c, w, v))
    return D(N, g(b), g(not b)), g(None)
@stmt('311')
def _(N, r):
    g = mc(N, 'box', [0], colOn(1, N, rx(r))); return D(N, g, g), []
@stmt('312')
def _(N, r):
    g = mc(N, 'hg', [0, 1], colOn(2, N, rx(r))); return D(N, g, g), []
@stmt('313')
def _(N, r):
    if N < 4: return None
    j = r.randrange(2, N - 1); g = mc(N, 'hg', [0, 1], blackOn(2, N))
    return D(N, g, swAt(N, j)), D(N, swAt(N, j), g)
@stmt('314')
def _(N, r):
    m = r.randrange(1, N)
    C = []
    for _ in range(6):
        g = r.choice(['H', 'Z', 'CZ', 'CH'])
        k = 1 if g in ('H', 'Z') else 2
        if m >= k: C.append((g, r.randrange(0, m - k + 1)))
    g = mc(N, 'hg', [m - 1, m], blackOn(m + 1, N))
    return D(N, C, g), D(N, g, C)
@stmt('315')
def _(N, r): return D(N, xAt(N, 0), B(N)), D(N, B(N), xAt(N, 0))
@stmt('316')
def _(N, r):
    if N < 2: return None
    g = mc(N, 'hg', [0, 1], blackOn(2, N)); return D(N, xAt(N, 0), g), D(N, g, xAt(N, 0))
@stmt('317')
def _(N, r):
    x = rx(r); a = mc(N, 'zx', [0], colOn(1, N, x)); b = mc(N, 'xz', [0], colOn(1, N, x))
    return D(N, a, b), D(N, b, a)  # both = id; check a b = b a (and a b = id separately)
@stmt('317id')
def _(N, r):
    x = rx(r); a = mc(N, 'zx', [0], colOn(1, N, x)); b = mc(N, 'xz', [0], colOn(1, N, x))
    return D(N, a, b), []
@stmt('333')
def _(N, r):
    if N < 3: return None
    g1 = mc(N, 'hg', [2, 0], U(ctlAt(1, True), blackOn(3, N)))
    g2 = mc(N, 'box', [1], U(ctlAt(0, True), blackOn(2, N)))
    return mc(N, 'zx', [0], blackOn(1, N)), D(N, g1, g2, g1, g2)

def comm(k, mk, need_ne=False):
    def f(N, r):
        if N < k + 1: return None
        x = rx(r); y = rx(r)
        if need_ne:
            if all(x(j) == y(j) for j in range(k, N)):
                return None
        p = [r.random() < 0.5 for _ in range(6)]
        g1, g2 = mk(N, colOn(k, N, x), colOn(k, N, y), p)
        return D(N, g1, g2), D(N, g2, g1)
    return f
EQS['335'] = comm(1, lambda N, X, Y, p: (mc(N, 'box', [0], X), mc(N, 'box', [0], Y)))
EQS['336'] = comm(2, lambda N, X, Y, p: (mc(N, 'box', [0], U(ctlAt(1, p[0]), X)), mc(N, 'box', [1], U(ctlAt(0, p[1]), Y))))
EQS['337'] = comm(2, lambda N, X, Y, p: (mc(N, 'box', [0], U(ctlAt(1, p[0]), X)), mc(N, 'hg', [0, 1], Y)), True)
EQS['338'] = comm(2, lambda N, X, Y, p: (mc(N, 'box', [0], U(ctlAt(1, p[0]), X)), mc(N, 'hg', [1, 0], Y)))
EQS['339'] = comm(3, lambda N, X, Y, p: (mc(N, 'box', [0], U(ctlAt(2, p[0]), ctlAt(1, p[1]), X)), mc(N, 'hg', [1, 2], U(ctlAt(0, p[2]), Y))), True)
EQS['340'] = comm(2, lambda N, X, Y, p: (mc(N, 'hg', [0, 1], X), mc(N, 'hg', [0, 1], Y)))
EQS['342'] = comm(3, lambda N, X, Y, p: (mc(N, 'hg', [0, 1], U(ctlAt(2, p[0]), X)), mc(N, 'hg', [0, 2], U(ctlAt(1, p[1]), Y))), True)
EQS['344'] = comm(3, lambda N, X, Y, p: (mc(N, 'hg', [0, 1], U(ctlAt(2, p[0]), X)), mc(N, 'hg', [1, 2], U(ctlAt(0, p[1]), Y))), True)
EQS['345'] = comm(2, lambda N, X, Y, p: (mc(N, 'hg', [1, 0], X), mc(N, 'hg', [0, 1], Y)))
EQS['346'] = comm(1, lambda N, X, Y, p: (mc(N, 'box', [0], X), mc(N, sgn(p[0]), [0], Y)))
EQS['347'] = comm(2, lambda N, X, Y, p: (mc(N, 'box', [0], U(ctlAt(1, p[1]), X)), mc(N, sgn(p[0]), [1], U(ctlAt(0, p[2]), Y))), True)
EQS['348'] = comm(2, lambda N, X, Y, p: (mc(N, 'hg', [0, 1], X), mc(N, sgn(p[0]), [0], U(ctlAt(1, p[1]), Y))), True)
EQS['349'] = comm(2, lambda N, X, Y, p: (mc(N, 'hg', [0, 1], X), mc(N, sgn(p[0]), [1], U(ctlAt(0, p[1]), Y))), True)
EQS['350'] = comm(3, lambda N, X, Y, p: (mc(N, 'hg', [0, 1], U(ctlAt(2, p[1]), X)), mc(N, sgn(p[0]), [2], U(ctlAt(1, p[2]), ctlAt(0, p[3]), Y))), True)
EQS['351'] = comm(1, lambda N, X, Y, p: (mc(N, sgn(p[0]), [0], X), mc(N, sgn(p[1]), [0], Y)))
EQS['352'] = comm(2, lambda N, X, Y, p: (mc(N, sgn(p[0]), [0], U(ctlAt(1, p[2]), X)), mc(N, sgn(p[1]), [1], U(ctlAt(0, p[3]), Y))), True)
# the negative controls: the x≠y hypotheses are needed
NEG = {'337': comm(2, lambda N, X, Y, p: (mc(N, 'box', [0], U(ctlAt(1, p[0]), X)), mc(N, 'hg', [0, 1], Y)))}

def _334(N, r):
    if N < 3: return None
    g1 = mc(N, 'hg', [2, 0], U(ctlAt(1, True), blackOn(3, N)))
    g2 = mc(N, 'box', [1], U(ctlAt(0, True), blackOn(2, N)))
    return mc(N, 'xz', [0], blackOn(1, N)), D(N, g2, g1, g2, g1)
EQS['334'] = _334

if __name__ == '__main__':
    r = random.Random(7)
    names = sys.argv[1:] or list(EQS)
    for name in names:
        f = EQS[name]; ok = 0; bad = 0
        for N in range(3, 7):
            for _ in range(8):
                res = f(N, r)
                if res is None: continue
                l, rr = res
                if np.allclose(mat(N, l), mat(N, rr)): ok += 1
                else:
                    bad += 1
        print(name, 'ok', ok, 'bad', bad)

