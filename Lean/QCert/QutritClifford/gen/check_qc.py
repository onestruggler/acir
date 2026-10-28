"""Check that the exact Pauli action of qc.py agrees with the matrices."""
import random
import numpy as np
import qc


def pauli_matrix(P, n):
    c, a, b = P
    dim = 3 ** n
    M = np.zeros((dim, dim), dtype=complex)
    for t in range(dim):
        d = [(t // 3 ** i) % 3 for i in range(n)]
        s = [(d[i] + a[i]) % 3 for i in range(n)]
        si = sum(s[i] * 3 ** i for i in range(n))
        M[si, t] = qc.W ** ((c + sum(b[i] * d[i] for i in range(n))) % 3)
    return M


def random_circ(n, length):
    out = []
    for _ in range(length):
        k = random.choice(['H', 'S', 'CZ', 'w'] if n > 1 else ['H', 'S', 'w'])
        if k == 'w':
            out.append(('w',))
        elif k == 'CZ':
            out.append(('CZ', random.randrange(n - 1)))
        else:
            out.append((k, random.randrange(n)))
    return out


def main():
    random.seed(1)
    for n in (1, 2, 3):
        for _ in range(200):
            w = random_circ(n, random.randrange(1, 12))
            U = qc.matrix(w, n)
            P = (random.randrange(3), tuple(random.randrange(3) for _ in range(n)),
                 tuple(random.randrange(3) for _ in range(n)))
            lhs = U @ pauli_matrix(P, n) @ U.conj().T
            rhs = pauli_matrix(qc.act(w, P), n)
            assert np.allclose(lhs, rhs, atol=1e-9), (n, w, P)
            assert np.allclose(U @ U.conj().T, np.eye(3 ** n), atol=1e-9)
    print("pauli action agrees with matrices")


if __name__ == '__main__':
    main()
