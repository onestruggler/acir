"""Geometry of the E8-lattice graph Gamma of the 3-wire CCX+H group.

A vertex is a group element g (coset g Theta, lattice g E).  Relative
position of two vertices g, h: the pi-exponents of h E relative to g E,
read off the matrix C = B^-1 g^T h B (B an E8 basis; g^-1 = g^T).
dist(g, h) = -min v_pi(C_ij), which is the Gamma-distance (adjacent iff 1).
Numbers: (a + b sqrt2) / 2^K as int pairs, K = 40 (tree.S).
"""
import random
from fractions import Fraction as F
from lat import G, e8_roots, orbit, THETA
from tree import word_matrix, mat_mul, S
from snf import basisE

BE = basisE()                       # basis vectors (rows)
Bcols = [list(r) for r in zip(*BE)] # B: columns = basis vectors -> B[i][j] = BE[j][i]
def _inv(M):
    n = len(M)
    aug = [M[i][:] + [F(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if aug[r][c] != 0)
        aug[c], aug[p] = aug[p], aug[c]
        pv = aug[c][c]; aug[c] = [x / pv for x in aug[c]]
        for r in range(n):
            if r != c and aug[r][c] != 0:
                f = aug[r][c]; aug[r] = [x - f*y for x, y in zip(aug[r], aug[c])]
    return [row[n:] for row in aug]
Binv = _inv(Bcols)
# integer versions: 2*B and Binv (Binv of E8 basis is integral? check) 
DEN_B = 2
B2 = [[int(Bcols[i][j] * 2) for j in range(8)] for i in range(8)]
import math
DI = 1
for r in Binv:
    for x in r: DI = DI * x.denominator // math.gcd(DI, x.denominator)
assert DI & (DI - 1) == 0
BI = [[int(x * DI) for x in r] for r in Binv]
EI = DI.bit_length() - 1

def transpose(M):  # M as cols[j][i]
    return [[M[i][j] for i in range(8)] for j in range(8)]

def vpi_int(a, b):
    """pi-valuation of (a + b sqrt2) for ints (not both 0)."""
    k = 0
    while a % 2 == 0:
        a, b = b, a // 2
        k += 1
    return k

def rel_dist(g, h):
    """Gamma distance between g E and h E."""
    # P = g^T h  (as cols): P e_j = g^T (h e_j)
    gT = transpose(g)
    P = mat_mul(gT, h)                 # entries scaled by S
    # C = Binv P B  -> compute with B2 (2B) : C*2*S = BI * P * B2
    # rows: (P B2)[i][j] = sum_k P[i][k] B2[k][j];  P[i][k] = cols[k][i]
    PB = [[(sum(P[k][i][0] * B2[k][j] for k in range(8)), sum(P[k][i][1] * B2[k][j] for k in range(8)))
           for j in range(8)] for i in range(8)]
    m = None
    for i in range(8):
        for j in range(8):
            a = sum(BI[i][k] * PB[k][j][0] for k in range(8))
            b = sum(BI[i][k] * PB[k][j][1] for k in range(8))
            if a == 0 and b == 0:
                continue
            v = vpi_int(a, b)
            if m is None or v < m:
                m = v
    # value scale: entries / (2 * S) = / 2^(K+1) = / pi^(2K+2)
    K = S.bit_length() - 1
    return -(m - (2 * K + 2 + 2 * EI))

I8 = word_matrix("")
E = frozenset(e8_roots())
H0E = frozenset(G["H0"](v) for v in E)
_ot = orbit(H0E, THETA)
REPS = list(_ot.values())                       # theta_i
T = [word_matrix((w + " H0").strip()) for w in REPS]

def d(g):
    return rel_dist(I8, g)

def neighbours(g):
    return [(i, mat_mul(g, Ti)) for i, Ti in enumerate(T)]

if __name__ == "__main__":
    print("d(I)", d(I8), "d(H0)", d(word_matrix("H0")), "d(CCZ)", d(word_matrix("H0 CCX0 H0")))
    print("d(H0 CCX1 H0)", d(word_matrix("H0 CCX1 H0")))
