"""Numerical model of the 3-qubit Toffoli-K / Sigma_1 gates (Amy-Ross-Wesley).

Basis state i = 4 x0 + 2 x1 + x2 (qubit 0 most significant).  Words are
tuples of letter names in operator order (the rightmost acts first), as
in the Agda development.  Matrices are 8x8 over Fractions, scaled by
nothing (K entries are +-1/2).
"""
from fractions import Fraction as Fr
import itertools

N = 8


def bits(i):
    return ((i >> 2) & 1, (i >> 1) & 1, i & 1)


def idx(b):
    return 4 * b[0] + 2 * b[1] + b[2]


def perm_matrix(f):
    """Matrix with entry 1 at (f(c), c)."""
    M = [[Fr(0)] * N for _ in range(N)]
    for c in range(N):
        M[f(c)][c] = Fr(1)
    return M


def diag_matrix(s):
    M = [[Fr(0)] * N for _ in range(N)]
    for c in range(N):
        M[c][c] = Fr(s(c))
    return M


def flip(j):
    def f(c):
        b = list(bits(c)); b[j] ^= 1; return idx(b)
    return f


def cx(j, k):
    def f(c):
        b = list(bits(c))
        if b[j]: b[k] ^= 1
        return idx(b)
    return f


def ccx(j, k):
    l = ({0, 1, 2} - {j, k}).pop()
    def f(c):
        b = list(bits(c))
        if b[j] and b[k]: b[l] ^= 1
        return idx(b)
    return f


def sw(j, k):
    def f(c):
        b = list(bits(c)); b[j], b[k] = b[k], b[j]; return idx(b)
    return f


def kmat(j, k):
    M = [[Fr(0)] * N for _ in range(N)]
    for r in range(N):
        for c in range(N):
            br, bc = bits(r), bits(c)
            l = ({0, 1, 2} - {j, k}).pop()
            if br[l] == bc[l]:
                s = (-1) ** (br[j] * bc[j] + br[k] * bc[k])
                M[r][c] = Fr(s, 2)
    return M


def nk():
    K = kmat(1, 2)
    M = [[Fr(0)] * N for _ in range(N)]
    for r in range(N):
        for c in range(N):
            if r < 4 and c < 4:
                M[r][c] = K[r][c]
            elif r >= 4 and c >= 4 and r == c:
                M[r][c] = Fr(1)
    return M


GATES = {
    'X0': perm_matrix(flip(0)), 'X1': perm_matrix(flip(1)), 'X2': perm_matrix(flip(2)),
    'Z0': diag_matrix(lambda c: -1 if bits(c)[0] else 1),
    'Z1': diag_matrix(lambda c: -1 if bits(c)[1] else 1),
    'Z2': diag_matrix(lambda c: -1 if bits(c)[2] else 1),
    'CX01': perm_matrix(cx(0, 1)), 'CX02': perm_matrix(cx(0, 2)),
    'CX10': perm_matrix(cx(1, 0)), 'CX12': perm_matrix(cx(1, 2)),
    'CX20': perm_matrix(cx(2, 0)), 'CX21': perm_matrix(cx(2, 1)),
    'CZ01': diag_matrix(lambda c: -1 if bits(c)[0] and bits(c)[1] else 1),
    'CZ02': diag_matrix(lambda c: -1 if bits(c)[0] and bits(c)[2] else 1),
    'CZ12': diag_matrix(lambda c: -1 if bits(c)[1] and bits(c)[2] else 1),
    'CCX01': perm_matrix(ccx(0, 1)), 'CCX02': perm_matrix(ccx(0, 2)),
    'CCX12': perm_matrix(ccx(1, 2)),
    'K01': kmat(0, 1), 'K12': kmat(1, 2),
    'SW01': perm_matrix(sw(0, 1)), 'SW02': perm_matrix(sw(0, 2)),
    'SW12': perm_matrix(sw(1, 2)),
    'NK': nk(),
    'CCZ': diag_matrix(lambda c: -1 if c == 7 else 1),
}

ID = [[Fr(int(r == c)) for c in range(N)] for r in range(N)]


def mul(A, B):
    return [[sum(A[r][k] * B[k][c] for k in range(N) if A[r][k]) for c in range(N)] for r in range(N)]


def mat(word):
    M = ID
    for l in word:
        M = mul(M, GATES[l])
    return M


def key(M):
    return tuple(tuple(r) for r in M)


def same(u, v):
    return mat(u) == mat(v)


def W(s):
    return tuple(s.split()) if isinstance(s, str) else tuple(s)


# Permutation-gate action on basis indices, for fast checks.
PERM = {}
for g, M in GATES.items():
    f = []
    ok = True
    for c in range(N):
        nz = [r for r in range(N) if M[r][c] != 0]
        if len(nz) != 1 or M[nz[0]][c] != 1:
            ok = False; break
        f.append(nz[0])
    if ok:
        PERM[g] = tuple(f)
