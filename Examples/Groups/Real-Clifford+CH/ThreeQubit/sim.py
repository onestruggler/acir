# Tiny exact-ish simulator for Real-Clifford+CH words on N wires.
# Wire 0 is the bottom wire; basis index bit w is the value of wire w.
# A word is a list of gates in time order (leftmost first), as in the
# Agda development; mat(word) is the matrix of the whole word.
import math
N = 3
D = 1 << N
S2 = 1 / math.sqrt(2)

def ident():
    return [[1.0 if i == j else 0.0 for j in range(D)] for i in range(D)]

def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(D)) for j in range(D)] for i in range(D)]

def one(w, m):
    """2x2 matrix m on wire w."""
    r = [[0.0] * D for _ in range(D)]
    for j in range(D):
        bj = (j >> w) & 1
        for bi in (0, 1):
            i = (j & ~(1 << w)) | (bi << w)
            r[i][j] += m[bi][bj]
    return r

def ctrl(c, val, g):
    """g applied when wire c has value val."""
    r = [[0.0] * D for _ in range(D)]
    for j in range(D):
        if ((j >> c) & 1) == val:
            for i in range(D):
                r[i][j] = g[i][j]
        else:
            r[j][j] = 1.0
    return r

Hm = [[S2, S2], [S2, -S2]]
Zm = [[1, 0], [0, -1]]
Xm = [[0, 1], [1, 0]]

def H(w): return [one(w, Hm)]
def Z(w): return [one(w, Zm)]
def X(w): return H(w) + Z(w) + H(w)
def CZ(a, b): return [ctrl(a, 1, one(b, Zm))]
def CH(c, t): return [ctrl(c, 1, one(t, Hm))]          # control c, target t
def wCH(c, t): return X(c) + CH(c, t) + X(c)           # white control
def wCZ(a, b): return X(a) + CZ(a, b) + X(a)           # white on a
def wwCZ(a, b): return X(a) + X(b) + CZ(a, b) + X(a) + X(b)
def SW(a, b):
    r = [[0.0] * D for _ in range(D)]
    for j in range(D):
        ba, bb = (j >> a) & 1, (j >> b) & 1
        i = (j & ~(1 << a) & ~(1 << b)) | (bb << a) | (ba << b)
        r[i][j] = 1.0
    return [r]
def PP(l, u): return (CH(u, l) + H(u) + Z(l)) * 3 + SW(l, u)

def mat(word):
    m = ident()
    for g in word:
        m = mul(g, m)          # time order: later gates multiply on the left
    return m

def eq(w1, w2, tol=1e-9):
    a, b = mat(w1), mat(w2)
    return all(abs(a[i][j] - b[i][j]) < tol for i in range(D) for j in range(D))

def comm(w1, w2): return eq(w1 + w2, w2 + w1)
def invol(w): return eq(w + w, [])
def rev(w): return list(reversed(w))
