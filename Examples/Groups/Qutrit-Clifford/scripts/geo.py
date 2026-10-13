"""The geometry of three-qutrit Clifford words, modulo two-wire facts.

Sp(6,3) acts on hyperbolic planes of F_3^6.  A = G01 x G2 is the stabiliser
of V2 (the Paulis of wire 2), B = G0 x G12 that of V0.  A word cut into
blocks alternately in A and in B is a path in the graph Gamma whose
vertices are A-planes and B-planes, adjacent when orthogonal; a relation
is a loop, and it follows from C15-C18 and two-wire facts exactly when
the loop is filled by translates of the loops of C15-C18.

Vectors: (x0, x1, x2, z0, z1, z2).  Pb(g) is the pull-back P -> g^-1 P g,
so that for words in time order Pb(uv) = Pb(u) Pb(v).
"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from qt import *

N = 3
F = 3

def vx(i): v = [0] * 6; v[i] = 1; return tuple(v)
def vz(i): v = [0] * 6; v[3 + i] = 1; return tuple(v)

def form(u, v):
    return (sum(u[i] * v[3 + i] - u[3 + i] * v[i] for i in range(3))) % 3

# ---------------------------------------------------------------- matrices
def mmul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(6)) % 3 for j in range(6)) for i in range(6))

def mvec(A, v):
    return tuple(sum(A[i][k] * v[k] for k in range(6)) % 3 for i in range(6))

I6 = tuple(tuple(1 if i == j else 0 for j in range(6)) for i in range(6))

def minv(A):
    # symplectic inverse: J^-1 A^T J
    J = [[0] * 6 for _ in range(6)]
    for i in range(3):
        J[i][3 + i] = 1
        J[3 + i][i] = 2
    Jt = tuple(tuple(J[i][j] for j in range(6)) for i in range(6))
    At = tuple(tuple(A[j][i] for j in range(6)) for i in range(6))
    Jinv = tuple(tuple((-J[i][j]) % 3 for j in range(6)) for i in range(6))
    R = mmul(mmul(Jinv, At), Jt)
    assert mmul(R, A) == I6, 'not symplectic'
    return R

# Pauli matrices over F_7, to read off the pull-backs exactly.
def pauli_word(v):
    c = []
    for w in range(3):
        c += Z(w) * v[3 + w] + X(w) * v[w]
    return c

_pk = {}
def _pauli_table():
    if _pk:
        return
    for v in itertools.product(range(3), repeat=6):
        M = mat(pauli_word(v), 3)
        for ph in range(3):
            f = pow(W, ph, P)
            _pk[key([[(f * x) % P for x in r] for r in M])] = v

def minv7(M):
    # inverse of a monomial-ish unitary over F_7 via Gauss
    n = len(M)
    A = [list(r) + [1 if i == j else 0 for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c])
        A[c], A[p] = A[p], A[c]
        iv = pow(A[c][c], P - 2, P)
        A[c] = [(x * iv) % P for x in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]
                A[r] = [(x - f * y) % P for x, y in zip(A[r], A[c])]
    return [r[n:] for r in A]

_pb = {}
def pb_token(tok):
    """Pull-back matrix of one token on three wires (columns: images of basis)."""
    if tok in _pb:
        return _pb[tok]
    _pauli_table()
    U = mat([tok], 3)
    Ui = minv7(U)
    cols = []
    for b in range(6):
        e = [0] * 6; e[b] = 1
        Pm = mat(pauli_word(e), 3)
        Q = mul(mul(Ui, Pm), U)
        cols.append(_pk[key(Q)])
    M = tuple(tuple(cols[j][i] for j in range(6)) for i in range(6))
    _pb[tok] = M
    return M

def pb_word(c):
    M = I6
    for tok in c:
        if tok[0] == 'nu':
            continue
        M = mmul(M, pb_token(tok))
    return M

# ---------------------------------------------------------------- planes
def rref(vecs):
    rows = [list(v) for v in vecs]
    out = []
    col = 0
    r = 0
    rows = [x for x in rows]
    for col in range(6):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][col]:
                piv = i; break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = 1 if rows[r][col] == 1 else 2
        rows[r] = [(x * iv) % 3 for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col]:
                f = rows[i][col]
                rows[i] = [(x - f * y) % 3 for x, y in zip(rows[i], rows[r])]
        r += 1
    return tuple(tuple(x) for x in rows[:r])

V2 = rref([vx(2), vz(2)])
V0 = rref([vx(0), vz(0)])
BASE = {'A': V2, 'B': V0}

def img(M, plane):
    return rref([mvec(M, v) for v in plane])

def orth(p, q):
    return all(form(u, v) == 0 for u in p for v in q)

# ---------------------------------------------------------------- blocks
def inv_tok(tok):
    k = tok[0]
    if k == 'H': return [tok] * 3
    if k == 'S': return [tok] * 2
    if k == 'CZ': return [tok] * 2
    if k == 'nu': return [tok] * 5
    raise ValueError(tok)

def inv_word(c):
    out = []
    for tok in reversed(c):
        out += inv_tok(tok)
    return out

def kind(tok):
    """'A' (wires 0,1 only), 'B' (wires 1,2 only), '*' (wire 1 or scalar)."""
    if tok[0] == 'nu': return '*'
    if tok[0] == 'CZ': return 'A' if tok[1] == 0 else 'B'
    w = tok[1]
    return {0: 'A', 1: '*', 2: 'B'}[w]

def blocks(c):
    """Cut a word into maximal blocks: letters of one kind commute past
    letters of the other kind on disjoint wires (wire 0 vs wire 2, CZ01
    vs wire 2, CZ12 vs wire 0) - here we only cut, never reorder."""
    bl = []
    for tok in c:
        k = kind(tok)
        if bl and (k == '*' or k == bl[-1][0]):
            bl[-1][1].append(tok)
        elif bl and bl[-1][0] == '*':
            bl[-1][0] = k
            bl[-1][1].append(tok)
        else:
            bl.append([k, [tok]])
    if bl and bl[0][0] == '*':
        bl[0][0] = 'A'
    return [(k, w) for k, w in bl]

def loop_of(c):
    """The vertex loop of a word that is the identity.  Returns the cyclic
    list of (type, plane)."""
    bl = blocks(c)
    # cyclic merge of first and last block if same type
    if len(bl) > 1 and bl[0][0] == bl[-1][0]:
        bl = [(bl[0][0], bl[-1][1] + bl[0][1])] + bl[1:-1]
        # (rotation: conjugating by the last block; harmless for the loop)
    M = I6
    verts = []
    for (k, w) in bl:
        verts.append((k, img(M, BASE[k])))
        M = mmul(M, pb_word(w))
    assert M == I6 or True
    return verts, bl

if __name__ == '__main__':
    from rules import RULES
    for name in ('C15', 'C16', 'C17', 'C18'):
        n, l, r = RULES[name]
        w = l + inv_word(r)
        assert pb_word(w) == I6, name
        verts, bl = loop_of(w)
        print(name, len(verts), [k for k, _ in verts])
        for i in range(len(verts)):
            a, b = verts[i], verts[(i + 1) % len(verts)]
            assert a[0] != b[0] and orth(a[1], b[1]), (name, i)
