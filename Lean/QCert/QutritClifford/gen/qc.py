"""Qutrit Clifford circuits: exact action on Pauli data, numeric matrices.

Conventions (as in the Lean development):
* wires are numbered from the bottom, wire 0 being the least significant
  digit of a basis index;
* a circuit is a list of letters in TIME order (first applied first); the
  Lean word, in operator order, is the reverse;
* letters: ('H', j), ('S', j) on wire j, ('CZ', j) on wires j, j + 1,
  ('w',) the scalar -omega.

Pauli data are (c, a, b): omega^c (x)_j X^{a_j} Z^{b_j}, with a, b tuples
indexed by the wire.  `act` is conjugation by a letter, exactly the Lean
`actGen` (act1 for H and S, actCZ for CZ).
"""
import itertools
import numpy as np

W = np.exp(2j * np.pi / 3)


def act_letter(letter, P):
    c, a, b = P
    a, b = list(a), list(b)
    if letter[0] == 'w':
        return (c, tuple(a), tuple(b))
    if letter[0] == 'H':
        j = letter[1]
        a0, b0 = a[j], b[j]
        c = (c + 2 * a0 * b0) % 3
        a[j], b[j] = (2 * b0) % 3, a0
    elif letter[0] == 'S':
        j = letter[1]
        a0, b0 = a[j], b[j]
        c = (c + a0 * (a0 - 1)) % 3
        b[j] = (b0 + 2 * a0) % 3
    elif letter[0] == 'CZ':
        j = letter[1]
        c = (c + a[j] * a[j + 1]) % 3
        b0, b1 = b[j], b[j + 1]
        b[j] = (b0 + a[j + 1]) % 3
        b[j + 1] = (b1 + a[j]) % 3
    return (c, tuple(a), tuple(b))


def act(circ, P):
    """Conjugation by a circuit in time order: the first letter acts first."""
    for letter in circ:
        P = act_letter(letter, P)
    return P


def pauli(n, c=0, **kw):
    """Pauli data on n wires; kw like z0=1, x1=2."""
    a = [0] * n
    b = [0] * n
    for k, v in kw.items():
        j = int(k[1:])
        if k[0] == 'x':
            a[j] = v % 3
        else:
            b[j] = v % 3
    return (c % 3, tuple(a), tuple(b))


# ---- matrices -------------------------------------------------------------

Hm = (1 / (W ** 2 - W)) * np.array([[1, 1, 1], [1, W, W ** 2], [1, W ** 2, W]])
Sm = np.diag([W, W, 1])


def gate_matrix(letter, n):
    dim = 3 ** n
    M = np.zeros((dim, dim), dtype=complex)
    if letter[0] == 'w':
        return -W * np.eye(dim)
    if letter[0] == 'CZ':
        j = letter[1]
        for t in range(dim):
            d = [(t // 3 ** i) % 3 for i in range(n)]
            M[t, t] = W ** (d[j] * d[j + 1])
        return M
    G = Hm if letter[0] == 'H' else Sm
    j = letter[1]
    for t in range(dim):
        d = [(t // 3 ** i) % 3 for i in range(n)]
        for s0 in range(3):
            e = list(d)
            e[j] = s0
            s = sum(e[i] * 3 ** i for i in range(n))
            M[s, t] += G[s0, d[j]]
    return M


def matrix(circ, n):
    M = np.eye(3 ** n, dtype=complex)
    for letter in circ:
        M = gate_matrix(letter, n) @ M
    return M


def same(c1, c2, n):
    return np.allclose(matrix(c1, n), matrix(c2, n), atol=1e-9)


# ---- words ----------------------------------------------------------------

def inv(circ):
    out = []
    for letter in reversed(circ):
        k = {'H': 3, 'S': 2, 'CZ': 2, 'w': 5}[letter[0]]
        out += [letter] * k
    return out


def up(circ, k=1):
    return [(l[0], l[1] + k) if l[0] != 'w' else l for l in circ]


def H(j=0):
    return [('H', j)]


def S(j=0):
    return [('S', j)]


def X(j=0):
    return H(j) + S(j) + H(j) * 2 + S(j) * 2 + H(j)


def Z(j=0):
    return H(j) * 2 + S(j) * 2 + H(j) * 2 + S(j)


def CZ(j=0):
    return [('CZ', j)]


def SWAP(j=0):
    hh = H(j) + H(j + 1)
    return hh + CZ(j) + hh + CZ(j) + hh + CZ(j)


def XC(j=0):
    """(D8): target on the top wire j + 1, control on wire j."""
    return H(j + 1) + CZ(j) + H(j + 1) * 3


def power(circ, k):
    return circ * k
