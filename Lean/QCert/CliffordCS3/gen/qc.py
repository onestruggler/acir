"""Exact matrices for Bian–Selinger's Clifford+CS circuits (arXiv:2306.08530).

Conventions as in `Syntax.lean`: words are in the order of matrix multiplication (the last
letter acts first); on three qubits the basis index is 4 q0 + 2 q1 + q2 (qubit 0 the most
significant); on two qubits (the fragment (a)-(c) on a pair) it is 2 u + l, `u` the upper
qubit of the pair.

All entries are dyadic Gaussian rationals, so complex floating point arithmetic is exact for
the words used here; `key` is an exact hashable form.
"""
import numpy as np

I2 = np.eye(2, dtype=complex)
KM = (1 / (1 + 1j)) * np.array([[1, 1], [1, -1]], dtype=complex)
SM = np.diag([1, 1j]).astype(complex)
XM = np.array([[0, 1], [1, 0]], dtype=complex)
CSM = np.diag([1, 1, 1, 1j]).astype(complex)


def kron(*ms):
    r = np.eye(1, dtype=complex)
    for m in ms:
        r = np.kron(r, m)
    return r


def key(m):
    a = np.round(m * (1 << 30))
    return a.real.astype(np.int64).tobytes() + a.imag.astype(np.int64).tobytes()


def eq(a, b):
    return np.array_equal(np.round(a * (1 << 30)), np.round(b * (1 << 30)))


def proportional(a, b):
    """a = c b for a scalar c (returns c or None)."""
    idx = np.unravel_index(np.argmax(np.abs(b)), b.shape)
    if abs(b[idx]) < 1e-12:
        return None
    c = a[idx] / b[idx]
    return c if np.allclose(a, c * b, atol=1e-9) else None


# ---------------------------------------------------------------- three qubits
GEN3 = ['i', 'K0', 'K1', 'K2', 'S0', 'S1', 'S2', 'C01', 'C12']
MAT3 = {
    'i': 1j * np.eye(8, dtype=complex),
    'K0': kron(KM, I2, I2), 'K1': kron(I2, KM, I2), 'K2': kron(I2, I2, KM),
    'S0': kron(SM, I2, I2), 'S1': kron(I2, SM, I2), 'S2': kron(I2, I2, SM),
    'C01': kron(CSM, I2), 'C12': kron(I2, CSM),
}
# ---------------------------------------------------------------- two qubits (a pair)
GEN2 = ['i', 'Ku', 'Kl', 'Su', 'Sl', 'CS']
MAT2 = {
    'i': 1j * np.eye(4, dtype=complex), 'Ku': kron(KM, I2), 'Kl': kron(I2, KM),
    'Su': kron(SM, I2), 'Sl': kron(I2, SM), 'CS': CSM.copy(),
}


def mat(word, M):
    n = next(iter(M.values())).shape[0]
    r = np.eye(n, dtype=complex)
    for g in word:
        r = r @ M[g]
    return r


def mat3(w): return mat(w, MAT3)
def mat2(w): return mat(w, MAT2)


# ---------------------------------------------------------------- Bian–Selinger's U_n generators
def two_level(n, j, k, U):
    m = np.eye(n, dtype=complex)
    m[j, j], m[j, k], m[k, j], m[k, k] = U[0, 0], U[0, 1], U[1, 0], U[1, 1]
    return m


def one_level(n, j, z):
    m = np.eye(n, dtype=complex)
    m[j, j] = z
    return m


def un_mat(n, g):
    """('X', j, k), ('K', j, k) with j < k, ('i', j)."""
    if g[0] == 'i':
        return one_level(n, g[1], 1j)
    if g[0] == 'X':
        return two_level(n, g[1], g[2], XM)
    return two_level(n, g[1], g[2], KM)


def un_word_mat(n, w):
    r = np.eye(n, dtype=complex)
    for g in w:
        r = r @ un_mat(n, g)
    return r


def perm_matrix(p):
    """The permutation matrix sending e_j to e_{p[j]}."""
    n = len(p)
    m = np.zeros((n, n), dtype=complex)
    for j in range(n):
        m[p[j], j] = 1
    return m


# ---------------------------------------------------------------- inverses
INV3 = {'i': ['i'] * 3, 'K0': ['K0', 'i'], 'K1': ['K1', 'i'], 'K2': ['K2', 'i'],
        'S0': ['S0'] * 3, 'S1': ['S1'] * 3, 'S2': ['S2'] * 3,
        'C01': ['C01'] * 3, 'C12': ['C12'] * 3}
INV2 = {'i': ['i'] * 3, 'Ku': ['Ku', 'i'], 'Kl': ['Kl', 'i'],
        'Su': ['Su'] * 3, 'Sl': ['Sl'] * 3, 'CS': ['CS'] * 3}


def inv(word, INV):
    out = []
    for g in reversed(word):
        out += INV[g]
    return out


for _g in GEN3:
    assert eq(mat3([_g] + INV3[_g]), np.eye(8))
for _g in GEN2:
    assert eq(mat2([_g] + INV2[_g]), np.eye(4))

if __name__ == '__main__':
    print('ok')
