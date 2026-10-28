"""Exact model of Algorithm 1 as formalized in Lean (QCert.LiRossSelinger).

States are n x n matrices over Q (Fractions); a word [g1,...,gm] acts as
g1 * ... * gm (rightmost first).  Generators: ('n',a), ('x',a,b), ('k',a,b,c,d).
"""
from fractions import Fraction as F
import random

def ident(n):
    return [[F(1) if i == j else F(0) for j in range(n)] for i in range(n)]

def gen_apply(g, M):
    """genMat g * M (row operations)."""
    M = [row[:] for row in M]
    if g[0] == 'n':
        a = g[1]
        M[a] = [-x for x in M[a]]
    elif g[0] == 'x':
        a, b = g[1], g[2]
        M[a], M[b] = M[b], M[a]
    else:
        a, b, c, d = g[1:]
        A, B, C, D = M[a], M[b], M[c], M[d]
        n = len(M)
        M[a] = [(A[j] + B[j] + C[j] + D[j]) / 2 for j in range(n)]
        M[b] = [(A[j] - B[j] + C[j] - D[j]) / 2 for j in range(n)]
        M[c] = [(A[j] + B[j] - C[j] - D[j]) / 2 for j in range(n)]
        M[d] = [(A[j] - B[j] - C[j] + D[j]) / 2 for j in range(n)]
    return M

def word_apply(w, M):
    for g in reversed(w):
        M = gen_apply(g, M)
    return M

def pivotJ(M):
    n = len(M)
    J = n
    while J > 0:
        i = J - 1
        if all(M[r][i] == (1 if r == i else 0) for r in range(n)):
            J -= 1
        else:
            break
    return J

def pcol(M):
    J = pivotJ(M)
    if J == 0:
        return [F(0)] * len(M)
    return [M[r][J - 1] for r in range(len(M))]

def lde_of(v):
    k = 0
    while not all((x * 2 ** k).denominator == 1 for x in v):
        k += 1
    return k

def wint(M):
    v = pcol(M)
    k = lde_of(v)
    return [int(x * 2 ** k) for x in v], k

def level(M):
    J = pivotJ(M)
    if J == 0:
        return (0, 0, 0)
    u, k = wint(M)
    nodd = 0 if k == 0 else sum(1 for x in u if x % 2)
    return (J, k, nodd)

def tau(z):
    return z % 4 == 3

def syll(M):
    J = pivotJ(M)
    if J == 0:
        return []
    u, k = wint(M)
    v = pcol(M)
    if k == 0:
        a = next(r for r in range(len(M)) if v[r] != 0)
        if a < J - 1:
            return [('x', a, J - 1)] + ([('n', a)] if v[a] < 0 else [])
        return [('n', J - 1)]
    odd = [r for r in range(len(M)) if u[r] % 2]
    a, b, c, d = odd[:4]
    return [('k', a, b, c, d)] + [('n', x) for x in (a, b, c, d) if tau(u[x])]

def nxt(M):
    return word_apply(syll(M), M)

def npath(m, M):
    """Syllables of the first m normal steps (leftmost latest)."""
    res = []
    for _ in range(m):
        s = syll(M)
        res = s + res
        M = word_apply(s, M)
    return res

def is_one(M):
    return pivotJ(M) == 0

def random_gen(n, rng):
    t = rng.random()
    if t < 0.15:
        return ('n', rng.randrange(n))
    if t < 0.45:
        a, b = sorted(rng.sample(range(n), 2))
        return ('x', a, b)
    return ('k',) + tuple(sorted(rng.sample(range(n), 4)))

def random_state(n, length, rng):
    M = ident(n)
    for _ in range(length):
        M = gen_apply(random_gen(n, rng), M)
    return M

def path_states(P, t):
    """States lift(P.drop i) * t for i = 0..len(P)."""
    return [word_apply(P[i:], t) for i in range(len(P) + 1)]

def check_square(s, g, m, P):
    """Check the square: npath m (g s) * g = P * syll s (as matrices on s),
    and that the inner states of P from next s lie below level s.
    Returns (ok_sem, bad_states)."""
    gs = gen_apply(g, s)
    lhs = word_apply(npath(m, gs) + [g], s)
    t = nxt(s)
    rhs = word_apply(P, t)
    ok = lhs == rhs
    L = level(s)
    bad = []
    sts = path_states(P, t)
    for i, st in enumerate(sts):
        if not level(st) < L:
            bad.append((i, level(st)))
    return ok, bad, L
