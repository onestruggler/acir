"""The four-wire relation R4 = (CCX(0;1,2) HH(0,3))^4 = CZ(1,2), exactly."""
from fractions import Fraction as F

N = 4
D = 1 << N

def bit(x, k): return x >> k & 1

def perm(f):
    return [[F(1) if f(j) == i else F(0) for j in range(D)] for i in range(D)]

def flip(t, cs=()):
    return perm(lambda j: j ^ (1 << t) if all(bit(j, c) for c in cs) else j)

def hh(a, b):
    M = [[F(0)] * D for _ in range(D)]
    for i in range(D):
        for j in range(D):
            if all(bit(i, k) == bit(j, k) for k in range(N) if k not in (a, b)):
                s = bit(i, a) * bit(j, a) + bit(i, b) * bit(j, b)
                M[i][j] = F(-1 if s % 2 else 1, 2)
    return M

def cz(a, b):
    return [[F(-1 if i == j and bit(i, a) and bit(i, b) else (1 if i == j else 0)) for j in range(D)] for i in range(D)]

def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(D)) for j in range(D)] for i in range(D)]

ccx = flip(0, (1, 2))
h03 = hh(0, 3)
m = mul(ccx, h03)
p = m
for _ in range(3):
    p = mul(p, m)
print("R4 holds:", p == cz(1, 2))
