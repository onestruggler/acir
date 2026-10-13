"""The normal boxes of Figure 9 (time order), and checks of Figure 8."""
from qt import *

def A(a, b, w=0):
    b = b % 3
    if (a, b) == (0, 1): return []
    if (a, b) == (0, 2): return H(w) * 2
    if a == 1: return S(w) * b + H(w)
    if a == 2: return H(w) * 2 + S(w) * ((2 * b) % 3) + H(w)
    raise ValueError((a, b))

def C(b, w=0): return X(w) * b
def E(b, w=0): return S(w) * b
def F(b, w=0): return Z(w) * ((2 * b) % 3)

# Two-wire boxes on wires w (bottom) and w+1 (top).
def B(a, b, w=0):
    B01 = SWAP(w) + CZ(w) + CZ(w) + XC(w)
    if (a, b) == (0, 0): return SWAP(w) + CZ(w)
    if (a, b) == (0, 1): return B01
    if (a, b) == (0, 2): return A(0, 2, w + 1) + CZ(w) + B01
    return A(a, b, w + 1) + CZ(w) * 2 + B01

def D(a, b, w=0):
    if a == 0: return SWAP(w) + CZ(w) * ((2 * b) % 3)
    return A(a, b, w) + D(0, 1, w)

# Paulis as matrices: ('P', a, b) on wire w is X^a Z^b (Z^b first).
def pauli(spec, n):
    """spec: dict wire -> (a, b); phase c: omega^c.  Returns matrix."""
    c = spec.get('c', 0)
    circ = []
    for w, ab in spec.items():
        if w == 'c': continue
        a, b = ab
        circ += Z(w) * b + X(w) * a
    M = mat(circ, n)
    f = pow(W, c, P)
    return [[(f * x) % P for x in r] for r in M]

def inv_mat(M):
    # Clifford matrices here are unitary up to the F7 conjugation; just
    # compute the inverse by powers: find k with M^k = I.
    n = len(M)
    I = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    acc = M
    prev = I
    for k in range(1, 10000):
        if acc == I:
            return prev
        prev = acc
        acc = mul(acc, M)
    raise ValueError

def conj(circ, Pm, n):
    U = mat(circ, n)
    return mul(mul(U, Pm), inv_mat(U))

def check(name, circ, n, pre, post):
    ok = conj(circ, pauli(pre, n), n) == pauli(post, n)
    if not ok:
        print('FAIL', name, pre, post)
    return ok

if __name__ == '__main__':
    allok = True
    for a in range(3):
        for b in range(3):
            if (a, b) != (0, 0):
                allok &= check(f'A{a}{b}', A(a, b), 1, {0: (a, b)}, {0: (0, 1)})
    for b in range(3):
        allok &= check(f'C{b}', C(b), 1, {0: (0, 1), 'c': b}, {0: (0, 1)})
        allok &= check(f'C{b}x', C(b), 1, {0: (1, 0)}, {0: (1, 0)})
        allok &= check(f'E{b}', E(b), 1, {0: (1, b)}, {0: (1, 0)})
        allok &= check(f'E{b}z', E(b), 1, {0: (0, 1)}, {0: (0, 1)})
        for i in range(3):
            allok &= check(f'F{b}', F(b), 1, {0: (1, i), 'c': b}, {0: (1, i)})
        allok &= check(f'F{b}z', F(b), 1, {0: (0, 1)}, {0: (0, 1)})
    for a in range(3):
        for b in range(3):
            # top = wire 1, bottom = wire 0
            allok &= check(f'B{a}{b}', B(a, b), 2, {1: (a, b), 0: (0, 1)}, {1: (0, 1), 0: (0, 0)})
            allok &= check(f'B{a}{b}x', B(a, b), 2,
                           {1: ((2 * a) % 3, (2 * b + a * a - 1) % 3), 0: (1, 0), 'c': (a * b) % 3},
                           {1: (1, 0), 0: (0, 0)})
            for i in range(3):
                allok &= check(f'D{a}{b}', D(a, b), 2, {1: (1, i), 0: (a, b)}, {1: (0, 0), 0: (1, i)})
            allok &= check(f'D{a}{b}z', D(a, b), 2, {1: (0, 1), 0: (0, 0)}, {1: (0, 0), 0: (0, 1)})
    print('all ok' if allok else 'FAILURES')
