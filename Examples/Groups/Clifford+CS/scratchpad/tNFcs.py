# BFS closure of the K-free fragment of P' at small N: the group of
# det-1 phased permutations should have order 4^(N-1) . N!
import csP, sys
from itertools import combinations
N = int(sys.argv[1]) if len(sys.argv) > 1 else 4
L = {}
for a, b in combinations(range(N), 2):
    for x, y in ((a, b), (b, a)):
        L[('iib', x, y)] = csP.matmul(csP.two_level(N, 'i', x), csP.minv('i', N, y))
for a in range(N):
    for b, c in combinations(range(N), 2):
        m = csP.matmul(csP.two_level(N, 'i', a), csP.two_level(N, 'i', a))
        L[('mX', a, b, c)] = csP.matmul(m, csP.two_level(N, 'X', b, c))
prs = list(combinations(range(N), 2))
for (a, b), (c, d) in combinations(prs, 2):
    if len({a, b, c, d}) == 4:
        L[('XX', a, b, c, d)] = csP.matmul(csP.two_level(N, 'X', a, b), csP.two_level(N, 'X', c, d))
seen = {csP.key(csP.ident(N))}
frontier = [csP.ident(N)]
while frontier:
    nxt = []
    for M in frontier:
        for lm in L.values():
            M2 = csP.matmul(M, lm)
            k = csP.key(M2)
            if k not in seen:
                seen.add(k); nxt.append(M2)
    frontier = nxt
import math
print(f'N={N}: closure {len(seen)}, expected 4^(N-1).N! = {4**(N-1)*math.factorial(N)}')
