"""Fast exact evaluation: each letter as an 8x8 integer matrix scaled by 2
(entries of K are +-1/2).  A word of length n is 2^n times its matrix; we
normalise by storing (matrix * 2^n) with n kept, and compare by cross
multiplying, or compute a canonical key by dividing out powers of 2."""
from model import LET, MAT, IDX

def scaled(M):
    return tuple(tuple(int(2 * x) for x in row) for row in M)

S = [scaled(MAT[x]) for x in LET]

def mm(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(8)) for j in range(8)) for i in range(8))

def key_of(M, n):
    # true matrix = M / 2^n ; canonical form: divide by 2 while all even and n > 0
    while n > 0 and all(x % 2 == 0 for row in M for x in row):
        M = tuple(tuple(x // 2 for x in row) for row in M)
        n -= 1
    return (M, n)

I8 = tuple(tuple(int(i == j) for j in range(8)) for i in range(8))

def val(word):
    M = I8
    for x in word:
        M = mm(M, S[x])
    return key_of(M, len(word))

# permutation-and-sign representation is impossible for K; use the key.
