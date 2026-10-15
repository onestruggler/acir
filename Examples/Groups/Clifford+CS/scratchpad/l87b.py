# Lemma 8.7 at n = 4: the spellings of X_j and K_j (and iI) over P'
# letters and earlier gates, checked as matrices in the Gray numbering.
#   X_j = Z_j . prod_e R_e    R_e the rotation on the edge e of direction j
#                             with its sign on the x_j = 1 end (lo or hi,
#                             so every decoded gadget has one orientation);
#                             the edges off the path are X^l-conjugates of
#                             path edges, l on the wires below j
#   K_j = prod_l X^l k X^l . X_j S_j X_j   k the hybrid at the first path
#                             edge of direction j, l over the other wires
#   iI  = X_0 S_0 X_0 S_0
# Words are read in written order: the matrix of u v is [u] [v].
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import combinations
import csP
from l87 import gcode, IDX, pos, flip

N = 16
def mp(*Ms):
    R = csP.ident(N)
    for M in Ms: R = csP.matmul(R, M)
    return R
def eq(A, B): return csP.key(A) == csP.key(B)
def i_(a): return csP.two_level(N, 'i', a)
def neg(a): return mp(i_(a), i_(a))
def iinv(a): return mp(i_(a), i_(a), i_(a))
def Xe(a, b): return csP.two_level(N, 'X', a, b)
def Ke(a, b): return csP.two_level(N, 'K', a, b)

# the gates in the Gray numbering
def perm(f):
    M = [[0j] * N for _ in range(N)]
    for k in range(N): M[IDX[f(gcode(k))]][k] = 1 + 0j
    return tuple(tuple(r) for r in M)
def diag(f):
    return tuple(tuple((1j ** (f(gcode(r)) % 4) if r == c else 0j) for c in range(N)) for r in range(N))
def X(j): return perm(lambda x: flip(x, j))
def S(j): return diag(lambda x: x[j])
def Z(j): return diag(lambda x: 2 * x[j])
def K(j):
    g = 1 / (1 + 1j)
    M = [[0j] * N for _ in range(N)]
    for k in range(N):
        x = gcode(k)
        if x[j]: continue
        u, v = k, IDX[flip(x, j)]
        M[u][u] = g; M[u][v] = g; M[v][u] = g; M[v][v] = -g
    return tuple(tuple(r) for r in M)
I4 = tuple(tuple((1j if r == c else 0j) for c in range(N)) for r in range(N))

# the consecutive letters
def lo(a): return mp(neg(a), Xe(a, a + 1))
def hi(a): return mp(neg(a + 1), Xe(a, a + 1))
def ki(a): return mp(Ke(a, a + 1), iinv(a))

def path_edges(j): return [a for a in range(15) if pos(a)[0] == j]
def rot_at(a, j):
    """the rotation at the path edge a of direction j, sign on the x_j = 1 end."""
    return lo(a) if gcode(a)[j] == 1 else hi(a)
def Xl(l):
    return mp(*[X(w) for w in l]) if l else csP.ident(N)
def subsets(ws):
    out = [()]
    for w in ws: out = out + [s + (w,) for s in out]
    return out

ok = True
for j in range(4):
    reps = path_edges(j)
    low = list(range(j))                       # wires fixed on the path edges
    body = mp(*[rot_at(a, j) for a in reps])
    rhs = mp(Z(j), *[mp(Xl(l), body, Xl(l)) for l in subsets(low)])
    r = eq(rhs, X(j)); ok &= r
    print('X', j, 'path edges', reps, 'conj over', low, r)
for j in range(4):
    a = path_edges(j)[0]
    assert gcode(a)[j] == 0
    others = [w for w in range(4) if w != j]
    rhs = mp(*[mp(Xl(l), ki(a), Xl(l)) for l in subsets(others)], X(j), S(j), X(j))
    r = eq(rhs, K(j)); ok &= r
    print('K', j, 'at', a, r)
r = eq(mp(X(0), S(0), X(0), S(0)), I4); ok &= r
print('iI', r)
print('ALL OK' if ok else 'FAILED')
