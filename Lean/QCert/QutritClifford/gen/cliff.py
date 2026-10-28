"""Exact projective qutrit Clifford elements, for the completeness generators.

A circuit is a list of letters in TIME order (as in qc.py): ('H', j),
('S', j), ('CZ', j) (wires j, j + 1).  Scalars are dropped: everything
here is up to a global phase.

A projective Clifford element on n wires is determined by the images of
the generators X_0, Z_0, ..., X_{n-1}, Z_{n-1} under conjugation, as exact
Pauli data (c, a, b); `key(w, n)` is that tuple.  Two circuits have the
same operator up to a phase exactly when their keys agree (Corollary B.3).
"""
from collections import deque
import qc


def gens(n):
    out = []
    for j in range(n):
        out.append(qc.pauli(n, **{'x%d' % j: 1}))
        out.append(qc.pauli(n, **{'z%d' % j: 1}))
    return out


def key(w, n):
    return tuple(qc.act(w, P) for P in gens(n))


def pmul(P, Q):
    """Product of Pauli data, as the Lean PD.mul."""
    c = (P[0] + Q[0] + sum(pb * qa for pb, qa in zip(P[2], Q[1]))) % 3
    a = tuple((x + y) % 3 for x, y in zip(P[1], Q[1]))
    b = tuple((x + y) % 3 for x, y in zip(P[2], Q[2]))
    return (c, a, b)


def apply_key(k, P):
    """The image of P under the element with generator images k."""
    n = len(P[1])
    r = (P[0], (0,) * n, (0,) * n)
    for j in range(n):
        for _ in range(P[1][j]):
            r = pmul(r, k[2 * j])
        for _ in range(P[2][j]):
            r = pmul(r, k[2 * j + 1])
    return r


def compose(k1, k2):
    """Key of w1 followed by w2 (time order), from their keys."""
    return tuple(apply_key(k2, P) for P in k1)


def ident(n):
    return tuple(gens(n))


def letters(n):
    out = []
    for j in range(n):
        out += [('H', j), ('S', j)]
    for j in range(n - 1):
        out.append(('CZ', j))
    return out


def inv(w):
    return qc.inv([l for l in w if l[0] != 'w'])


def strip(w):
    return [l for l in w if l[0] != 'w']


def wires(l):
    if l[0] == 'CZ':
        return {l[1], l[1] + 1}
    if l[0] == 'w':
        return set()
    return {l[1]}


def commute(l1, l2):
    return not (wires(l1) & wires(l2))


def bfs_words(n, alphabet=None, start=None):
    """Shortest word for every element (BFS over the projective group)."""
    alphabet = alphabet or letters(n)
    start = start or ident(n)
    lk = {l: key([l], n) for l in alphabet}
    seen = {start: []}
    q = deque([start])
    while q:
        k = q.popleft()
        w = seen[k]
        for l in alphabet:
            k2 = compose(k, lk[l])
            if k2 not in seen:
                seen[k2] = w + [l]
                q.append(k2)
    return seen
