"""The local structure of the mixed atom J0 = M_0 X_12 K_0123 on four
wires: its order, and its centraliser in the signed permutations."""
import sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent / 'wn'))
from fractions import Fraction as Fr
import itertools
D = 16
def ident(): return [[Fr(int(i == j)) for j in range(D)] for i in range(D)]
def mul(a, b): return [[sum(a[i][k] * b[k][j] for k in range(D)) for j in range(D)] for i in range(D)]
def M(a):
    m = ident(); m[a][a] = Fr(-1); return m
def X(a, b):
    m = ident(); m[a][a] = m[b][b] = Fr(0); m[a][b] = m[b][a] = Fr(1); return m
def K(A):
    m = ident()
    for r in A:
        for c in A: m[r][c] = Fr(0)
    for i, r in enumerate(A):
        for j, c in enumerate(A): m[r][c] = Fr((-1) ** bin(i & j).count('1'), 2)
    return m
J = mul(mul(M(0), X(1, 2)), K((0, 1, 2, 3)))
P, n = J, 1
while P != ident():
    P = mul(P, J); n += 1
print('order of J0:', n)
# J restricted to the block {0,1,2,3}
print('block:', [[str(J[r][c]) for c in range(4)] for r in range(4)])
# signed permutations of the block {0..3} commuting with J's block (the rest is free)
blk = [[J[r][c] for c in range(4)] for r in range(4)]
cnt = 0; gens = []
for perm in itertools.permutations(range(4)):
    for signs in itertools.product((1, -1), repeat=4):
        S = [[Fr(signs[r]) if perm[c] == r else Fr(0) for c in range(4)] for r in range(4)]
        SB = [[sum(S[r][k] * blk[k][c] for k in range(4)) for c in range(4)] for r in range(4)]
        BS = [[sum(blk[r][k] * S[k][c] for k in range(4)) for c in range(4)] for r in range(4)]
        if SB == BS:
            cnt += 1; gens.append((perm, signs))
print('signed permutations of the block commuting with it:', cnt)
for g in gens: print('  ', g)
