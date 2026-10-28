"""The macro level: letters T0..T6 (X_[i,i+1]), N ((-1)_[0]), K (K_[0,1,2,3]).

encM g is the macro word whose image under phi is enc g."""
from kb import KB

NT = 7
NL, KL = 7, 8      # letters N, K
MNAME = [f"T{i}" for i in range(7)] + ["N", "K"]

def xGapM(g, a):
    if g == 0:
        return [a]
    return [a] + xGapM(g - 1, a + 1) + [a]

def xabM(a, b):
    return xGapM(b - a - 1, a)

def conjXM(i, j, u):
    return u if i == j else xabM(i, j) + u + xabM(i, j)

def encM(g):
    if g[0] == 'n':
        c = g[1]
        return [NL] if c == 0 else xabM(0, c) + [NL] + xabM(0, c)
    if g[0] == 'x':
        return xabM(g[1], g[2])
    a, b, c, d = g[1:]
    return conjXM(0, a, conjXM(1, b, conjXM(2, c, conjXM(3, d, [KL]))))

def encMW(word):
    out = []
    for g in word:
        out += encM(g)
    return out

# ---------------------------------------------------------------- base equations
# Coxeter axioms (index order as in Lean): sq i, far i j (i+2<=j), braid i
def coxeter_axioms():
    ax = []
    for i in range(7):
        ax.append((("sq", i), (i, i), ()))
    for i in range(7):
        for j in range(i + 2, 7):
            ax.append((("far", i, j), (i, j), (j, i)))
    for i in range(6):
        ax.append((("braid", i), (i, i + 1, i), (i + 1, i, i + 1)))
    return ax

def N_(a): return ('n', a)
def X_(a, b): return ('x', a, b)
def K_(a, b, c, d): return ('k', a, b, c, d)

def fig7_axioms():
    ng = lambda c: encM(N_(c))
    x = lambda a, b: encM(X_(a, b))
    k = lambda a, b, c, d: encM(K_(a, b, c, d))
    Kc = [KL]
    rho = k(4, 5, 6, 7) + Kc + x(3, 4) + Kc + k(4, 5, 6, 7)
    R = [
        (83, ng(0) + ng(0), []),
        (84, Kc + Kc, []),
        (85, x(1, 2) + ng(0), ng(0) + x(1, 2)),
        (86, x(2, 3) + ng(0), ng(0) + x(2, 3)),
        (87, x(3, 4) + ng(0), ng(0) + x(3, 4)),
        (88, x(4, 5) + ng(0), ng(0) + x(4, 5)),
        (89, x(5, 6) + ng(0), ng(0) + x(5, 6)),
        (90, x(6, 7) + ng(0), ng(0) + x(6, 7)),
        (91, x(4, 5) + Kc, Kc + x(4, 5)),
        (92, x(5, 6) + Kc, Kc + x(5, 6)),
        (93, x(6, 7) + Kc, Kc + x(6, 7)),
        (94, ng(4) + Kc, Kc + ng(4)),
        (95, ng(0) + ng(4), ng(4) + ng(0)),
        (96, Kc + k(4, 5, 6, 7), k(4, 5, 6, 7) + Kc),
        (97, x(0, 1) + Kc, Kc + x(1, 3) + ng(1) + ng(3)),
        (98, x(1, 2) + Kc, ng(0) + Kc + ng(0) + Kc + ng(0)),
        (99, x(2, 3) + Kc, Kc + x(1, 3)),
        (100, Kc + k(1, 3, 4, 5), k(2, 3, 4, 5) + k(0, 1, 2, 4)),
        (101, ng(0) + ng(4) + x(0, 4) + rho, rho + x(0, 4) + ng(4) + ng(0)),
    ]
    return [(("fig7", n), tuple(l), tuple(r)) for n, l, r in R]

# ---------------------------------------------------------------- semantics (permutation part)
def perm_word(w):
    """permutation of a T-word read as a matrix product: s -> image"""
    p = list(range(8))
    # matrix product M1 M2 ... ; acts on e_s as M1(M2(...(e_s)))
    for t in reversed(w):
        assert t < 7
        q = list(range(8)); q[t], q[t + 1] = q[t + 1], q[t]
        p = [q[p[s]] for s in range(8)]
    return tuple(p)
