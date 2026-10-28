"""Model of Amy-Ross-Wesley's Sigma_1 and Li-Ross-Selinger's G_8, as in the Lean files.

Matrices are 8x8 over Fractions; state of |x0 x1 x2> is 4 x0 + 2 x1 + x2.
Words are read left to right as matrix products.
"""
from fractions import Fraction as F
from itertools import combinations, permutations

LET = ["X0", "X1", "X2", "CX01", "CX02", "CX10", "CX12", "CX20", "CX21",
       "CCX01", "CCX02", "CCX12", "Z0", "Z1", "Z2", "CZ01", "CZ02", "CZ12",
       "K01", "K12", "S01", "S02", "S12", "Kc", "CCZ"]
IDX = {n: i for i, n in enumerate(LET)}

def bits(s):
    return ((s >> 2) & 1, (s >> 1) & 1, s & 1)

def st(b):
    return 4 * b[0] + 2 * b[1] + b[2]

def perm_mat(f):
    # matrix with M[f(s)][s] = 1 : column s maps to f(s)
    M = [[F(0)] * 8 for _ in range(8)]
    for s in range(8):
        M[f(s)][s] = F(1)
    return M

def diag(sg):
    M = [[F(0)] * 8 for _ in range(8)]
    for s in range(8):
        M[s][s] = F(sg(s))
    return M

def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(8)) for j in range(8)] for i in range(8)]

def ident():
    return [[F(int(i == j)) for j in range(8)] for i in range(8)]

def xq(j):
    def f(s):
        b = list(bits(s)); b[j] ^= 1; return st(b)
    return perm_mat(f)

def cx(c, t):
    def f(s):
        b = list(bits(s))
        if b[c]: b[t] ^= 1
        return st(b)
    return perm_mat(f)

def ccx(c1, c2):
    t = 3 - c1 - c2
    def f(s):
        b = list(bits(s))
        if b[c1] and b[c2]: b[t] ^= 1
        return st(b)
    return perm_mat(f)

def zq(j):
    return diag(lambda s: -1 if bits(s)[j] else 1)

def cz(j, k):
    return diag(lambda s: -1 if bits(s)[j] and bits(s)[k] else 1)

def swapq(j, k):
    def f(s):
        b = list(bits(s)); b[j], b[k] = b[k], b[j]; return st(b)
    return perm_mat(f)

def kq(j, k):
    # H_j H_k
    M = [[F(0)] * 8 for _ in range(8)]
    for r in range(8):
        for c in range(8):
            br, bc = bits(r), bits(c)
            other = 3 - j - k
            if br[other] != bc[other]:
                continue
            sgn = (-1) ** (br[j] * bc[j] + br[k] * bc[k])
            M[r][c] = F(sgn, 2)
    return M

def kc():
    # K_[0,1,2,3]: K on states 0..3, identity on 4..7
    M = ident()
    for r in range(4):
        for c in range(4):
            sgn = (-1) ** bin(r & c).count("1")
            M[r][c] = F(sgn, 2)
    return M

MAT = {
    "X0": xq(0), "X1": xq(1), "X2": xq(2),
    "CX01": cx(0, 1), "CX02": cx(0, 2), "CX10": cx(1, 0), "CX12": cx(1, 2),
    "CX20": cx(2, 0), "CX21": cx(2, 1),
    "CCX01": ccx(0, 1), "CCX02": ccx(0, 2), "CCX12": ccx(1, 2),
    "Z0": zq(0), "Z1": zq(1), "Z2": zq(2),
    "CZ01": cz(0, 1), "CZ02": cz(0, 2), "CZ12": cz(1, 2),
    "K01": kq(0, 1), "K12": kq(1, 2),
    "S01": swapq(0, 1), "S02": swapq(0, 2), "S12": swapq(1, 2),
    "Kc": kc(), "CCZ": diag(lambda s: -1 if s == 7 else 1),
}

def key(M):
    return tuple(tuple(r) for r in M)

def ev(word):
    M = ident()
    for x in word:
        M = mul(M, MAT[x])
    return M

def eq(u, v):
    return ev(u) == ev(v)

# ---------------------------------------------------------------- abbreviations
def xAdj(a):
    return {0: ["X0", "X1", "CCX01", "X1", "X0"],
            1: ["X0", "CCX01", "CCX02", "CCX01", "X0"],
            2: ["X0", "CCX01", "X0"],
            3: ["X0", "X2", "CCX01", "X0", "CCX12", "CCX02", "CCX12", "X0", "CCX01", "X2", "X0"],
            4: ["X1", "CCX01", "X1"],
            5: ["CCX01", "CCX02", "CCX01"]}.get(a, ["CCX01"])

def xGap(g, a):
    if g == 0:
        return xAdj(a)
    return xAdj(a) + xGap(g - 1, a + 1) + xAdj(a)

def xab(a, b):
    return xGap(b - a - 1, a)

NEG0 = ["X0", "X1", "X2", "CCZ", "X2", "X1", "X0"]

def negw(c):
    return NEG0 if c == 0 else xab(0, c) + NEG0 + xab(0, c)

def conjX(i, j, u):
    return u if i == j else xab(i, j) + u + xab(i, j)

def kw(a, b, c, d):
    return conjX(0, a, conjX(1, b, conjX(2, c, conjX(3, d, ["Kc"]))))

RHO = kw(4, 5, 6, 7) + ["Kc"] + xab(3, 4) + ["Kc"] + kw(4, 5, 6, 7)

# ---------------------------------------------------------------- LRS level
# generators as tuples: ('n', a), ('x', a, b), ('k', a, b, c, d)

def lmat(g):
    M = ident()
    if g[0] == 'n':
        M[g[1]][g[1]] = F(-1)
    elif g[0] == 'x':
        a, b = g[1], g[2]
        M[a][a] = M[b][b] = F(0); M[a][b] = M[b][a] = F(1)
    else:
        idx = g[1:]
        for r in range(4):
            for c in range(4):
                sgn = (-1) ** bin(r & c).count("1")
                M[idx[r]][idx[c]] = F(sgn, 2)
    return M

def lev(word):
    M = ident()
    for g in word:
        M = mul(M, lmat(g))
    return M

def enc(g):
    if g[0] == 'n':
        return negw(g[1])
    if g[0] == 'x':
        return xab(g[1], g[2])
    return kw(*g[1:])

def encw(word):
    out = []
    for g in word:
        out += enc(g)
    return out

N = lambda a: ('n', a)
X = lambda a, b: ('x', a, b)
K = lambda a, b, c, d: ('k', a, b, c, d)

def table1(n=8):
    R = []  # (family, indices, lhs, rhs)
    rng = range(n)
    for a, b in combinations(rng, 2):
        R.append(("1a", (a, b), [X(a, b), X(a, b)], []))
    for a in rng:
        R.append(("1b", (a,), [N(a), N(a)], []))
    for q in combinations(rng, 4):
        R.append(("1c", q, [K(*q), K(*q)], []))
    for a, b in combinations(rng, 2):
        for c, d in combinations(rng, 2):
            if len({a, b, c, d}) == 4:
                R.append(("2a", (a, b, c, d), [X(a, b), X(c, d)], [X(c, d), X(a, b)]))
    for a, b in combinations(rng, 2):
        for c in rng:
            if c not in (a, b):
                R.append(("2b", (a, b, c), [X(a, b), N(c)], [N(c), X(a, b)]))
    for a, b in combinations(rng, 2):
        for q in combinations(rng, 4):
            if not set(q) & {a, b}:
                R.append(("2c", (a, b) + q, [X(a, b), K(*q)], [K(*q), X(a, b)]))
    for a in rng:
        for b in rng:
            if a != b:
                R.append(("2d", (a, b), [N(a), N(b)], [N(b), N(a)]))
    for a in rng:
        for q in combinations(rng, 4):
            if a not in q:
                R.append(("2e", (a,) + q, [N(a), K(*q)], [K(*q), N(a)]))
    for q in combinations(rng, 4):
        for p in combinations(rng, 4):
            if not set(q) & set(p):
                R.append(("2f", q + p, [K(*q), K(*p)], [K(*p), K(*q)]))
    for a, a2, b in combinations(rng, 3):
        R.append(("3a", (a, a2, b), [X(a, a2), X(a, b)], [X(a2, b), X(a, a2)]))
    for a, b, b2 in combinations(rng, 3):
        R.append(("3b", (a, b, b2), [X(b, b2), X(a, b)], [X(a, b2), X(b, b2)]))
    for a, b in combinations(rng, 2):
        R.append(("3c", (a, b), [X(a, b), N(b)], [N(a), X(a, b)]))
    for a, a2, b, c, d in combinations(rng, 5):
        R.append(("3d", (a, a2, b, c, d), [X(a, a2), K(a, b, c, d)], [K(a2, b, c, d), X(a, a2)]))
    for a, b, b2, c, d in combinations(rng, 5):
        R.append(("3e", (a, b, b2, c, d), [X(b, b2), K(a, b, c, d)], [K(a, b2, c, d), X(b, b2)]))
    for a, b, c, c2, d in combinations(rng, 5):
        R.append(("3f", (a, b, c, c2, d), [X(c, c2), K(a, b, c, d)], [K(a, b, c2, d), X(c, c2)]))
    for a, b, c, d, d2 in combinations(rng, 5):
        R.append(("3g", (a, b, c, d, d2), [X(d, d2), K(a, b, c, d)], [K(a, b, c, d2), X(d, d2)]))
    for a, b, c, d in combinations(rng, 4):
        R.append(("4a", (a, b, c, d), [X(a, b), K(a, b, c, d)], [K(a, b, c, d), X(b, d), N(b), N(d)]))
        R.append(("4b", (a, b, c, d), [X(b, c), K(a, b, c, d)],
                  [N(a), K(a, b, c, d), N(a), K(a, b, c, d), N(a)]))
        R.append(("4c", (a, b, c, d), [X(c, d), K(a, b, c, d)], [K(a, b, c, d), X(b, d)]))
    for a, b, c, d, e, f in combinations(rng, 6):
        R.append(("5a", (a, b, c, d, e, f), [K(a, b, c, d), K(b, d, e, f)], [K(c, d, e, f), K(a, b, c, e)]))
    for a, b, c, d, e, f, g, h in combinations(rng, 8):
        core = [K(e, f, g, h), K(a, b, c, d), X(d, e), K(a, b, c, d), K(e, f, g, h)]
        R.append(("6a", (a, b, c, d, e, f, g, h),
                  [N(a), N(e), X(a, e)] + core + [X(a, e), N(a), N(e)], core))
    return R

if __name__ == "__main__":
    R = table1()
    from collections import Counter
    c = Counter(r[0] for r in R)
    print(len(R), sorted(c.items()))
    bad = [r for r in R if lev(r[2]) != lev(r[3])]
    print("unsound LRS:", len(bad))
    # encoding check on generators
    gens = set()
    for r in R:
        for g in r[2] + r[3]:
            gens.add(g)
    print("gens", len(gens), all(ev(enc(g)) == lmat(g) for g in gens))
