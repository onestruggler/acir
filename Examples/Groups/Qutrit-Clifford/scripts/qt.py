"""Qutrit Clifford circuits, exactly, over F_7.

F_7 contains a primitive cube root of unity (w = 2) and 1/(w^2 - w) = 1/2 = 4,
and reduction mod 7 is faithful on the finite Clifford groups here, so equality
of matrices over F_7 decides equality of the complex matrices.

Wires: wire 0 is the bottom wire, the least significant digit of an index
(the paper's last tensor factor).  Circuits are lists of tokens in TIME order
(as drawn, left to right); `mat` returns the operator (last token leftmost).

Tokens: ('H',w) ('S',w) ('CZ',w) [CZ on wires w, w+1] ('nu',) [the scalar -w].
"""
P = 7
W = 2           # omega
HS = 4          # 1/(w^2 - w)
NU = (-W) % P   # -omega


def dim(n):
    return 3 ** n


def digit(x, w):
    return (x // 3 ** w) % 3


def ident(n):
    d = dim(n)
    return [[1 if i == j else 0 for j in range(d)] for i in range(d)]


def mul(A, B):
    n = len(A)
    m = len(B[0])
    k = len(B)
    C = [[0] * m for _ in range(n)]
    for i in range(n):
        Ai = A[i]
        Ci = C[i]
        for t in range(k):
            a = Ai[t]
            if a:
                Bt = B[t]
                for j in range(m):
                    Ci[j] += a * Bt[j]
        for j in range(m):
            Ci[j] %= P
    return C


def apply_token(tok, M, n):
    """Return G * M where G is the matrix of tok on n wires."""
    d = dim(n)
    kind = tok[0]
    if kind == 'nu':
        return [[(NU * x) % P for x in row] for row in M]
    if kind == 'S':
        w = tok[1]
        out = []
        for i in range(d):
            f = W if digit(i, w) in (0, 1) else 1
            out.append([(f * x) % P for x in M[i]])
        return out
    if kind == 'Z':
        w = tok[1]
        out = []
        for i in range(d):
            f = pow(W, digit(i, w), P)
            out.append([(f * x) % P for x in M[i]])
        return out
    if kind == 'CZ':
        w = tok[1]
        out = []
        for i in range(d):
            f = pow(W, digit(i, w) * digit(i, w + 1), P)
            out.append([(f * x) % P for x in M[i]])
        return out
    if kind == 'H':
        w = tok[1]
        s = 3 ** w
        out = [[0] * len(M[0]) for _ in range(d)]
        for i in range(d):
            xi = digit(i, w)
            base = i - xi * s
            for k in range(3):
                c = (HS * pow(W, xi * k, P)) % P
                row = M[base + k * s]
                oi = out[i]
                for j in range(len(row)):
                    oi[j] += c * row[j]
        return [[x % P for x in row] for row in out]
    raise ValueError(tok)


def mat(circ, n):
    M = ident(n)
    for tok in circ:
        M = apply_token(tok, M, n)
    return M


def key(M):
    return tuple(tuple(r) for r in M)


def eq(c1, c2, n):
    return mat(c1, n) == mat(c2, n)


# ---------------------------------------------------------------- macros
def H(w=0):  return [('H', w)]
def S(w=0):  return [('S', w)]
def CZ(w=0): return [('CZ', w)]
def nu(k=1): return [('nu',)] * k
def pw(c, k): return c * k

def minus1(): return nu(3)          # D1
def omega(): return nu(4)           # D2
def Sp(w=0): return H(w) * 2 + S(w) + H(w) * 2          # D3  S' = H^2 S H^2
def X(w=0):  return H(w) + S(w) + H(w) * 2 + S(w) * 2 + H(w)   # D4
def Z(w=0):  return H(w) * 2 + S(w) * 2 + H(w) * 2 + S(w)      # D5
def HH(w=0): return H(w) + H(w + 1)
def SWAP(w=0):                       # D6, on wires w, w+1
    return HH(w) + CZ(w) + HH(w) + CZ(w) + HH(w) + CZ(w)
def CX(w=0):                         # D7: control on top (w+1), target bottom (w)
    return H(w) + CZ(w) + H(w) * 3
def XC(w=0):                         # D8: control on bottom (w), target top (w+1)
    return H(w + 1) + CZ(w) + H(w + 1) * 3
# Three wires: top = wire 2, middle = 1, bottom = 0.
def CZ02():                          # D9: SWAP on bottom two, CZ on top two, SWAP
    return SWAP(0) + CZ(1) + SWAP(0)
def CX20():                          # D10: control top, target bottom
    return SWAP(0) + CX(1) + SWAP(0)
def XC02():                          # D11: target top, control bottom
    return SWAP(1) + XC(0) + SWAP(1)


def gate_diag_ok():
    # sanity: Z and X as matrices
    Zm = mat(Z(0), 1)
    Xm = mat(X(0), 1)
    assert Zm == [[1, 0, 0], [0, W, 0], [0, 0, W * W % P]], Zm
    assert Xm == [[0, 0, 1], [1, 0, 0], [0, 1, 0]], Xm
    Spm = mat(Sp(0), 1)
    assert Spm == [[W, 0, 0], [0, 1, 0], [0, 0, W]], Spm
