"""Half-subgroups of W(E8) on three wires, directly: the 4x4 blocks U
(on a face) such that U (+) I preserves the 240 roots."""
import sys, itertools
from fractions import Fraction as F
from e8 import root_orbit

roots = set(root_orbit())
def face_pts(w, b):
    return [x for x in range(8) if (x >> w & 1) == b]

def matmul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)) for i in range(4))

# generators: signed transpositions and a sign, and K = (1/2) H(x)H
I4 = tuple(tuple(F(int(i == j)) for j in range(4)) for i in range(4))
def perm_m(p):
    return tuple(tuple(F(int(p[j] == i)) for j in range(4)) for i in range(4))
def sign_m(k):
    return tuple(tuple(F(-1 if (i == j == k) else int(i == j)) for j in range(4)) for i in range(4))
K = tuple(tuple(F((-1) ** bin(i & j).count('1'), 2) for j in range(4)) for i in range(4))
gens = [perm_m((1, 0, 2, 3)), perm_m((0, 2, 1, 3)), perm_m((0, 1, 3, 2)), sign_m(0), K]
grp = {I4}
fr = [I4]
while fr:
    nw = []
    for A in fr:
        for g in gens:
            B = matmul(A, g)
            if B not in grp:
                grp.add(B); nw.append(B)
    fr = nw
    if len(grp) > 100000:
        print('too big'); break
print('candidate group order', len(grp))

for w in range(3):
    for b in (0, 1):
        P = face_pts(w, b)
        ok = 0
        for U in grp:
            good = True
            for r in roots:
                v = list(r)
                sub = [v[x] for x in P]
                img = [sum(U[i][j] * sub[j] for j in range(4)) for i in range(4)]
                v2 = list(v)
                for i, x in enumerate(P):
                    v2[x] = img[i]
                if any(F(c).denominator != 1 for c in v2) or tuple(int(c) for c in v2) not in roots:
                    good = False; break
            ok += good
        print(f'half (w={w}, b={b}): {ok} elements preserve E8')
