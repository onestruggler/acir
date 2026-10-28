"""Bian and Selinger's two-level generators in dimension 4 as two-wire CliffCS₂ circuits.

Basis index s0 + 2 s1 (wire 0 the least significant bit).  Each generator is a conjugate of
an atom on the indices 2, 3 (`CS` for i_[3], the CNOT for X_[2,3], the controlled K for
K_[2,3]) by a permutation circuit that carries 2, 3 to its indices in order."""
import numpy as np, itertools
import cscliff as C
from cscliff import L

W = [('w', 0)]
H0, H1, S0, S1, CS, SW = L('H'), L('H', 1), L('S'), L('S', 1), L('CS'), L('SW')
X0 = [H0, S0, S0, H0]
X1 = [H1, S1, S1, H1]
CXa = [H0, CS, CS, H0]                       # control wire 1, target wire 0
RCX = [SW] + CXa + [SW]                      # control wire 0, target wire 1
CK = [S1, S1, S1, CS, H0, CS, H0, CS]        # K on wire 0 when wire 1 is set
ATOM = {'i': [CS], 'X': CXa, 'K': CK}

def perm_of(word):
    """The permutation of the basis indices a permutation circuit realises."""
    M = C.mat(2, word)
    p = {}
    for j in range(4):
        col = M[:, j]
        k = int(np.argmax(abs(col)))
        assert abs(abs(col[k]) - 1) < 1e-9
        p[j] = k
    return p

TOKENS = {'X0': X0, 'X1': X1, 'CX': CXa, 'RCX': RCX, 'SW': [SW]}

def inv(word):
    """The inverse of a word of self-inverse permutation letters (reversed)."""
    return list(reversed(word))

# permutation circuits as products of tokens; find, for each target (a, b), a shortest
# product carrying 2 -> a, 3 -> b
def find_frame(a, b):
    for n in range(0, 4):
        for ts in itertools.product(sorted(TOKENS), repeat=n):
            w = []
            for t in ts: w += TOKENS[t]
            p = perm_of(w) if w else {j: j for j in range(4)}
            if p[2] == a and p[3] == b: return list(ts), w
    raise Exception((a, b))

def conj(P, A):
    """P A P⁻¹ in time order: P⁻¹ first."""
    return inv(P) + A + P

FRAMES = {}
for a in range(4):
    for b in range(a + 1, 4):
        FRAMES[(a, b)] = find_frame(a, b)
I_FRAMES = {a: find_frame(a, (a + 1) % 4 if a != 3 else 2) for a in range(4)}

def dec(g):
    """The decoding of a generator: ('X', a, b), ('K', a, b), ('i', a), or ('w',)."""
    if g[0] == 'w': return W
    if g[0] == 'i':
        a = g[1]
        # i_[a]: CS conjugated by a permutation sending 3 to a
        for n in range(0, 4):
            for ts in itertools.product(sorted(TOKENS), repeat=n):
                w = []
                for t in ts: w += TOKENS[t]
                p = perm_of(w) if w else {j: j for j in range(4)}
                if p[3] == a: return conj(w, ATOM['i'])
    ts, w = FRAMES[(g[1], g[2])]
    return conj(w, ATOM[g[0]])

def gen_mat(g):
    """The two-level matrix of a generator."""
    M = np.eye(4, dtype=complex)
    if g[0] == 'w': return C.w8 * M
    if g[0] == 'i': M[g[1], g[1]] = 1j; return M
    a, b = g[1], g[2]
    U = np.array([[0, 1], [1, 0]]) if g[0] == 'X' else C.w8 ** 7 * C.MH
    M[a, a], M[a, b], M[b, a], M[b, b] = U[0, 0], U[0, 1], U[1, 0], U[1, 1]
    return M

if __name__ == '__main__':
    for a in range(4):
        g = ('i', a); assert np.allclose(C.mat(2, dec(g)), gen_mat(g)), g
    for (a, b) in FRAMES:
        for t in 'XK':
            g = (t, a, b); assert np.allclose(C.mat(2, dec(g)), gen_mat(g)), g
        print((a, b), FRAMES[(a, b)][0], len(dec(('K', a, b))))
    print('ok')
