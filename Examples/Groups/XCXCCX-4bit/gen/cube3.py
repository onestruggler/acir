"""Cube symmetries on three wires, for transporting relations of edge Toffolis.

States are ints, bit w = wire w.  An edge Toffoli is the transposition of
two states differing in one bit.  A symmetry is a word in X0, X1, X2, SW0,
SW1; conjugating a circuit c by a symmetry word s, as s c s⁻¹ in diagram
order, moves the transposition (a b) of c to (s⁻¹ a, s⁻¹ b).
"""
import os
import sys
from collections import deque
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xc import perm  # noqa: E402
from derive import parse, show  # noqa: E402

GRAY = [0b000, 0b001, 0b011, 0b010, 0b110, 0b111, 0b101, 0b100]
SYMS = ['X0', 'X1', 'X2', 'SW0', 'SW1']


def sym_words():
    """Shortest word for each of the 48 symmetries, keyed by permutation."""
    ident = tuple(range(8))
    words = {ident: ()}
    q = deque([ident])
    while q:
        p = q.popleft()
        for g in SYMS:
            w = words[p] + (g,)
            p2 = perm(parse(' '.join(w)), 3)
            if p2 not in words:
                words[p2] = w
                q.append(p2)
    return words


def inv_perm(p):
    q = [0] * len(p)
    for i, v in enumerate(p):
        q[v] = i
    return tuple(q)


def edge(d):
    return frozenset((GRAY[d], GRAY[d + 1]))


def transport(base, target, words):
    """Symmetry words s with s c s⁻¹ moving the base edges onto the target edges, in order."""
    out = []
    for p, w in words.items():
        pi = inv_perm(p)   # s⁻¹ as a function of states
        if all(frozenset(pi[x] for x in b) == t for b, t in zip(base, target)):
            out.append(w)
    return sorted(out, key=len)


def inverse_word(w):
    return tuple(reversed(w))      # every symmetry letter is an involution


if __name__ == '__main__':
    W = sym_words()
    print('symmetries', len(W))
    for i in range(7):
        for j in range(i + 2, 7):
            ei, ej = edge(i), edge(j)
            if ei & ej:
                continue
            s = transport([edge(1), edge(4)], [ei, ej], W)
            print('far%d%d' % (i, j), ' '.join(s[0]) if s else None)
    for i in range(6):
        s = transport([edge(4), edge(5)], [edge(i), edge(i + 1)], W)
        print('braid%d' % i, ' '.join(s[0]) if s else None)
