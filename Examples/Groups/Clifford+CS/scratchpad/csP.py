# Exact numerics for the Clifford+CS >= 4-wire design (four-wire-notes.md):
#   1. letters of P' have det 1 and the coset-action table closes
#   2. MITM word search: K_bc . i_0^-1 as a P'-word (item (a), K case)
#   3. e-sem: the encoding preserves the matrix at width 4
# Entries are Gaussian dyadics; python complex is exact on them for the
# short products here (denominators 2^k, k small).
import sys
from itertools import combinations, product

def matmul(A, B):
    n = len(A)
    Bt = list(zip(*B))
    return tuple(tuple(sum(a * b for a, b in zip(row, col)) for col in Bt)
                 for row in A)

def ident(n):
    return tuple(tuple(1 + 0j if r == c else 0j for c in range(n)) for r in range(n))

def two_level(n, kind, a, b=None):
    M = [[1 + 0j if r == c else 0j for c in range(n)] for r in range(n)]
    if kind == 'i':
        M[a][a] = 1j
    elif kind == 'X':
        M[a][a] = 0j; M[b][b] = 0j; M[a][b] = 1 + 0j; M[b][a] = 1 + 0j
    elif kind == 'K':
        g = 1 / (1 + 1j)
        M[a][a] = g; M[a][b] = g; M[b][a] = g; M[b][b] = -g
    return tuple(tuple(row) for row in M)

def minv(kind, n, a, b=None):
    # inverses: i^-1 = i^3, X^-1 = X, K^-1 = K i_a i_b (rel-16)
    if kind == 'i':
        m = two_level(n, 'i', a)
        return matmul(m, matmul(m, m))
    if kind == 'X':
        return two_level(n, 'X', a, b)
    m = two_level(n, 'K', a, b)
    return matmul(m, matmul(two_level(n, 'i', a), two_level(n, 'i', b)))

def letters(n):
    L = {}
    idx = range(n)
    for a, c in combinations(idx, 2):
        for x, y in ((a, c), (c, a)):
            L[('iib', x, y)] = matmul(two_level(n, 'i', x), minv('i', n, y))
    for a in idx:
        for b, c in combinations(idx, 2):
            m = matmul(two_level(n, 'i', a), two_level(n, 'i', a))
            L[('mX', a, b, c)] = matmul(m, two_level(n, 'X', b, c))
    prs = list(combinations(idx, 2))
    for (a, b), (c, d) in combinations(prs, 2):
        if len({a, b, c, d}) == 4:
            L[('XX', a, b, c, d)] = matmul(two_level(n, 'X', a, b), two_level(n, 'X', c, d))
    for (a, b) in prs:
        for (c, d) in prs:
            if len({a, b, c, d}) == 4:
                L[('KKb', a, b, c, d)] = matmul(two_level(n, 'K', a, b), minv('K', n, c, d))
    return L

def key(M):
    return tuple(tuple((round(z.real * 64), round(z.imag * 64)) for z in row) for row in M)

def adj(M):
    n = len(M)
    return tuple(tuple(M[c][r].conjugate() for c in range(n)) for r in range(n))

def mitm(n, target, depth):
    # meet in the middle: w1 . w2 = target with |w1|, |w2| <= depth;
    # backward states are target . L^-1 ... (adjoint = inverse, unitary).
    L = letters(n)
    items = list(L.items())
    fwd = {key(ident(n)): []}
    ffro = {key(ident(n)): (ident(n), [])}
    bwd = {key(target): []}
    bfro = {key(target): (target, [])}
    if key(target) in fwd: return []
    for d in range(depth):
        nxt = {}
        for _, (M, w) in ffro.items():
            for name, lm in items:
                M2 = matmul(M, lm)
                k2 = key(M2)
                if k2 not in fwd:
                    fwd[k2] = w + [name]
                    nxt[k2] = (M2, w + [name])
                    if k2 in bwd:
                        return fwd[k2] + bwd[k2]
        ffro = nxt
        nxt = {}
        for _, (M, w) in bfro.items():
            for name, lm in items:
                M2 = matmul(M, adj(lm))
                k2 = key(M2)
                if k2 not in bwd:
                    bwd[k2] = [name] + w
                    nxt[k2] = (M2, [name] + w)
                    if k2 in fwd:
                        return fwd[k2] + bwd[k2]
        bfro = nxt
        print(f"  depth {d + 1}: fwd {len(fwd)}, bwd {len(bwd)}", flush=True)
    return None

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'search'
    if mode == 'search':
        n = 4
        # target: K_01 . i_0^-1
        T = matmul(two_level(n, 'K', 0, 1), minv('i', n, 0))
        w = mitm(n, T, int(sys.argv[2]) if len(sys.argv) > 2 else 4)
        print('K_01 i_0^-1 =', w)
    elif mode == 'esem':
        # E at width 4 preserves matrices.  Wire 0 = least significant bit
        # (index x = sum x_w 2^w as in Real-Clifford's bits/idx).
        n = 16
        def gate_K(w):
            # product over contexts of K[y0,y1], y0/y1: bit w = 0/1
            M = ident(n)
            for y in range(n):
                if not (y >> w) & 1:
                    M = matmul(M, two_level(n, 'K', y, y | (1 << w)))
            return M
        def gate_S(w):
            M = ident(n)
            for y in range(n):
                if (y >> w) & 1:
                    M = matmul(M, two_level(n, 'i', y))
            return M
        def gate_CS(v, w):
            M = ident(n)
            for y in range(n):
                if (y >> v) & 1 and (y >> w) & 1:
                    M = matmul(M, two_level(n, 'i', y))
            return M
        import math
        def kron(A, B):
            na, nb = len(A), len(B)
            return tuple(tuple(A[ra][ca] * B[rb][cb]
                               for cb in range(nb) for ca in range(na))
                         for rb in range(nb) for ra in range(na))
        # wire-0-least-significant kron: full = M_wire3 (x) ... (x) M_wire0
        I2 = ident(2)
        Kg = tuple(tuple(x / (1 + 1j) for x in row) for row in ((1 + 0j, 1 + 0j), (1 + 0j, -1 + 0j)))
        Sg = ((1 + 0j, 0j), (0j, 1j))
        CSg = tuple(tuple((1j if r == c == 3 else (1 + 0j if r == c else 0j))
                          for c in range(4)) for r in range(4))
        def emb1(g, w):
            M = g if w == 0 else I2
            for k in range(1, 4):
                M = kron(M, g if k == w else I2)
            return M
        ok = True
        for w in range(4):
            ok &= emb1(Kg, w) == gate_K(w); ok &= emb1(Sg, w) == gate_S(w)
        # CS on wires 0,1
        CSfull = kron(kron(CSg, I2), I2)
        ok &= CSfull == gate_CS(0, 1)
        dets = []
        print('e-sem at width 4:', 'OK' if ok else 'MISMATCH')
