"""Shortest words over the permutation gates for elements of S8."""
from collections import deque
from model import PERM, W
from rels import T

PG = [g for g in ['X0', 'X1', 'X2', 'CX01', 'CX02', 'CX10', 'CX12', 'CX20', 'CX21',
                  'CCX01', 'CCX02', 'CCX12', 'SW01', 'SW02', 'SW12'] if g in PERM]
IDP = tuple(range(8))


def comp(f, g):
    """Operator order: (f g)(c) = f(g(c))."""
    return tuple(f[g[c]] for c in range(8))


def pw(word):
    p = IDP
    for l in word:
        p = comp(p, PERM[l])
    return p


def shortest_all(gens=PG):
    dist = {IDP: ()}
    q = deque([IDP])
    while q:
        p = q.popleft()
        for g in gens:
            np = comp(p, PERM[g])
            if np not in dist:
                dist[np] = dist[p] + (g,)
                q.append(np)
    return dist


def transposition(a, b):
    l = list(range(8)); l[a], l[b] = b, a; return tuple(l)


if __name__ == '__main__':
    D = shortest_all()
    print(len(D))
    for i in range(7):
        t = transposition(i, i + 1)
        assert pw(T(i)) == t, i
        print(i, ' '.join(D[t]), '   T:', ' '.join(T(i)))
    import collections
    print(collections.Counter(len(w) for w in D.values()))
