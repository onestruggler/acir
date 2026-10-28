"""Sections of the two Schreier stages, and the local facts they need.

Time order throughout; letters as in qc.py; projective (scalars dropped).

Stage 1 (base point [Z0]): sigma(p) for a non-zero point p = (a, b)
(a, b tuples over the wires), built from the bottom wire up:
  sigma(p) = alpha(p0)                    if p is zero above wire 0,
           = Gamma(p0) ; up sigma(p^)     otherwise,
with alpha(a, b) : Z -> X^a Z^b on one wire, Gamma(a, b) : Z0 -> X^a Z^b Z1
on two wires (Gamma(a, b) = A ; alpha(a, b) for (a, b) != 0, A = H^3 CZ H
on wire 0, and Gamma(0, 0) = SWAP).

Stage 2 (inside K1 = Stab[Z0]; base point [X0]): for q = (1, i) (+) q^,
  tau(q) = Q(i)                        if q^ = 0,
         = Q(i) ; CZ ; up sigma(q^)     otherwise,  Q(i) = S^(2i) on wire 0.

K1 letters: S0, X0, Z0, CZ01, every letter above wire 0.
K2 letters: X0, Z0, every letter above wire 0.
"""
from collections import deque
import cliff
import qc

ALPHA = {
    (0, 1): [], (0, 2): ['H', 'H'], (1, 0): ['H', 'H', 'H'],
    (1, 1): ['H', 'H', 'H', 'S', 'S'], (1, 2): ['H', 'H', 'H', 'S'],
    (2, 0): ['H'], (2, 1): ['H', 'H', 'H', 'S', 'H', 'H'], (2, 2): ['H', 'S', 'H'],
}


def alpha(a, b, j=0):
    return [(g, j) for g in ALPHA[(a, b)]]


def A(j=0):
    return [('H', j)] * 3 + [('CZ', j)] + [('H', j)]


def Gamma(a, b, j=0):
    if (a, b) == (0, 0):
        return qc.SWAP(j)
    return A(j) + alpha(a, b, j)


def Q(i):
    return [('S', 0)] * (2 * i)


def X(j=0):
    return qc.X(j)


def Z(j=0):
    return qc.Z(j)


def sigma(a, b, j=0):
    """Section on wires j.. of the point (a, b) (full-length tuples)."""
    n = len(a)
    if all(a[k] == 0 and b[k] == 0 for k in range(j + 1, n)):
        return alpha(a[j], b[j], j)
    return Gamma(a[j], b[j], j) + sigma(a, b, j + 1)


def tau(i, a, b):
    """Stage-2 section of (1, i) (+) (a, b) restricted to wires 1.."""
    n = len(a)
    if all(a[k] == 0 and b[k] == 0 for k in range(1, n)):
        return Q(i)
    return Q(i) + [('CZ', 0)] + sigma(a, b, 1)


def proj(P):
    return (P[1], P[2])


def act_point(w, p):
    a, b = p
    return proj(qc.act(w, (0, a, b)))


def check_alpha():
    for (a, b), _ in ALPHA.items():
        assert proj(qc.act(alpha(a, b), (0, (0,), (1,)))) == ((a,), (b,))
        assert qc.act(alpha(a, b), (0, (0,), (1,)))[0] == 0


def check_sections(n):
    import itertools
    Z0 = ((0,) * n, (1,) + (0,) * (n - 1))
    X0 = ((1,) + (0,) * (n - 1), (0,) * n)
    for a in itertools.product(range(3), repeat=n):
        for b in itertools.product(range(3), repeat=n):
            if any(a) or any(b):
                assert act_point(sigma(a, b), Z0) == (a, b), (a, b)
    for i in range(3):
        for a in itertools.product(range(3), repeat=n - 1):
            for b in itertools.product(range(3), repeat=n - 1):
                aa, bb = (1,) + a, (i,) + b
                w = tau(i, aa, bb)
                assert act_point(w, X0) == (aa, bb)
                assert act_point(w, Z0) == Z0


# ---- K-words by breadth-first search in the small stabilisers ----------

K1_LETTERS = {
    'S0': [('S', 0)], 'X0': qc.X(0), 'Z0': qc.Z(0), 'C0': [('CZ', 0)],
    'H1': [('H', 1)], 'S1': [('S', 1)], 'H2': [('H', 2)], 'S2': [('S', 2)],
    'C1': [('CZ', 1)],
}
K2_NAMES = ['X0', 'Z0', 'H1', 'S1', 'H2', 'S2', 'C1']
K1_NAMES = ['S0', 'X0', 'Z0', 'C0', 'H1', 'S1', 'H2', 'S2', 'C1']


def kword(names):
    out = []
    for nm in names:
        out += K1_LETTERS[nm]
    return out


def bfs_k(names, n):
    """Shortest K-word (list of letter names) for each element."""
    names = [nm for nm in names if all(max(cliff.wires(l), default=0) < n
                                       for l in K1_LETTERS[nm])]
    lk = {nm: cliff.key(K1_LETTERS[nm], n) for nm in names}
    start = cliff.ident(n)
    seen = {start: []}
    q = deque([start])
    while q:
        k = q.popleft()
        for nm in names:
            k2 = cliff.compose(k, lk[nm])
            if k2 not in seen:
                seen[k2] = seen[k] + [nm]
                q.append(k2)
    return seen


if __name__ == '__main__':
    check_alpha()
    for n in (1, 2, 3):
        check_sections(n)
    print('sections ok')
    K1_2 = bfs_k(K1_NAMES, 2)
    K2_2 = bfs_k(K2_NAMES, 2)
    print('|K1(2)| =', len(K1_2), '|K2(2)| =', len(K2_2))
