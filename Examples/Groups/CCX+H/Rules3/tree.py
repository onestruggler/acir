"""Is the graph of E8-lattices (E ~ theta H0 E) a tree near E?

Fixed-point exact arithmetic: a number is (a + b sqrt2) / 2^K, K = 40.
A group element is an 8x8 matrix of such numbers (columns = images of e_j).
Vertex gE is keyed by the hash of its root set g R.
"""
import sys, itertools, hashlib
from lat import G, vec, e8_roots, orbit, THETA
from fractions import Fraction as F

K = 40
S = 1 << K

def fx(x):  # (Fraction a, Fraction b) -> scaled ints
    a, b = x
    A = a * S; B = b * S
    assert A.denominator == 1 and B.denominator == 1
    return (int(A), int(B))

def word_matrix(word):
    cols = []
    for j in range(8):
        v = vec([1 if i == j else 0 for i in range(8)])
        for g in reversed(word.split()):  # matrix-product order: rightmost acts first
            v = G[g](v)
        cols.append([fx(c) for c in v])
    return cols  # cols[j][i]

def mat_mul(M, N):  # (M N) columns: (MN) e_j = M (N e_j)
    out = []
    for j in range(8):
        col = []
        Nj = N[j]
        for i in range(8):
            a = b = 0
            for k in range(8):
                ma, mb = M[k][i]; na, nb = Nj[k]
                a += ma * na + 2 * mb * nb
                b += ma * nb + mb * na
            assert a % S == 0 and b % S == 0
            col.append((a // S, b // S))
        out.append(col)
    return out

ROOTS = e8_roots()
RI = [[fx(c) for c in r] for r in ROOTS]

def key(M):
    vs = []
    for r in RI:
        v = []
        for i in range(8):
            a = b = 0
            for k in range(8):
                ra, rb = r[k]
                if ra == 0 and rb == 0: continue
                ma, mb = M[k][i]
                a += ma * ra + 2 * mb * rb
                b += ma * rb + mb * ra
            v.append(a // S); v.append(b // S)
        vs.append(tuple(v))
    vs.sort()
    return hashlib.sha1(repr(vs).encode()).digest()

if __name__ == "__main__":
    E = frozenset(ROOTS)
    H0E = frozenset(G["H0"](v) for v in E)
    ot = orbit(H0E, THETA)   # lattice -> word w with lattice = w H0 E  (w applied left)
    reps = list(ot.values())
    print("neighbours:", len(reps), flush=True)
    T = [word_matrix((w + " H0").strip()) for w in reps]
    I = word_matrix("")
    kE = key(I)
    seen = {kE: (0, "")}
    lvl1 = []
    for i, Ti in enumerate(T):
        k = key(Ti)
        assert k not in seen
        seen[k] = (1, i); lvl1.append((Ti, i))
    print("level 1 distinct:", len(lvl1), flush=True)
    # level 2 from v1 = H0 E only (by transitivity on edges at E): H0 * T_j
    T0 = [Ti for Ti, i in lvl1 if reps[i] == ""]
    assert len(T0) == 1
    M1 = T0[0]
    hits = 0
    lvl2 = []
    for j, Tj in enumerate(T):
        M2 = mat_mul(M1, Tj)
        k = key(M2)
        if k in seen:
            d, info = seen[k]
            if not (d == 0):
                hits += 1
                print("collision at level 2 via", repr(reps[j]), "with", d, info, flush=True)
        else:
            lvl2.append((M2, j))
    print("level 2 new from H0E:", len(lvl2), "hits", hits, flush=True)
