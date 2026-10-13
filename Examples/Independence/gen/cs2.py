"""The two-level relations of Bian and Selinger on four indices
(Examples.Groups.Clifford+CS-TwoLevel.Syntactics at n = 4), and their
decoding into CliffCS₂ on two wires: each generator a frame's
conjugate of CS (the phases), the CNOT CX01 (the exchanges) or the
controlled K CK01 (the K's).

Index k = 2 x₀ + x₁, wire 0 the most significant bit.  The decoding of
a generator is a scalar-free circuit with exactly its matrix (each
two-level generator is a symmetric matrix, so the order of reading does
not matter for one generator): the phases i_[a] as diagonal words in CS,
S0, S1 (and ω² for a = 0), the exchanges X_[a,b] as CNOTs, the swap or
the swap with both wires negated, and K_[a,b] as the controlled K
CK01 = CS H1 CS H1 CS S0³ (control wire 0, K on wire 1), conjugated."""
import itertools
import cliffCS
import circ

CK01 = 'CS01 H1 CS01 H1 CS01 S0 S0 S0'
CK10 = 'CS01 H0 CS01 H0 CS01 S1 S1 S1'

# The frames: permutation circuits taking the canonical pair (2, 3) to
# each pair (a, b), 2 to a and 3 to b, and the index 3 to each index a.
FRAME = {(2, 3): [], (0, 1): ['X0'], (1, 3): ['SW01'], (0, 2): ['X1', 'SW01'],
         (1, 2): ['CX01', 'SW01'], (0, 3): ['X1', 'CX01', 'SW01']}
IFRAME = {3: [], 2: ['X1'], 1: ['X0'], 0: ['X0', 'X1']}


def conj(F, C):
    return ' '.join(list(F) + [C] + list(reversed(F)))


DI = {a: conj(IFRAME[a], 'CS01') for a in IFRAME}
DX = {p: conj(FRAME[p], 'CX01') for p in FRAME}
DK = {p: conj(FRAME[p], CK01) for p in FRAME}


def i(j): return [('i', j)]
def X(j, k): return [('X', j, k)]
def K(j, k): return [('K', j, k)]


def dec(word):
    out = []
    for g in word:
        if g[0] == 'i':
            out.append(DI[g[1]])
        elif g[0] == 'X':
            out.append(DX[(g[1], g[2])])
        else:
            out.append(DK[(g[1], g[2])])
    return ' '.join(out)


R = {}
J = range(4)
P = [(a, b) for a in J for b in J if a < b]
for j in J:
    R['order-i %d' % j] = (i(j) * 4, [])
for (j, k) in P:
    R['order-X %d%d' % (j, k)] = (X(j, k) * 2, [])
    R['order-K %d%d' % (j, k)] = (K(j, k) * 8, [])
for j in J:
    for k in J:
        if j != k:
            R['comm-ii %d %d' % (j, k)] = (i(j) + i(k), i(k) + i(j))
for j in J:
    for (k, l) in P:
        if j not in (k, l):
            R['comm-iX %d %d%d' % (j, k, l)] = (i(j) + X(k, l), X(k, l) + i(j))
            R['comm-iK %d %d%d' % (j, k, l)] = (i(j) + K(k, l), K(k, l) + i(j))
for (j, k) in P:
    for (l, m) in P:
        if len({j, k, l, m}) == 4:
            R['comm-XX %d%d %d%d' % (j, k, l, m)] = (X(j, k) + X(l, m), X(l, m) + X(j, k))
            R['comm-XK %d%d %d%d' % (j, k, l, m)] = (X(j, k) + K(l, m), K(l, m) + X(j, k))
            R['comm-KK %d%d %d%d' % (j, k, l, m)] = (K(j, k) + K(l, m), K(l, m) + K(j, k))
for (j, k) in P:
    R['swap-iX %d%d' % (j, k)] = (i(k) + X(j, k), X(j, k) + i(j))
    R['rel-13 %d%d' % (j, k)] = (K(j, k) + i(k) * 2, X(j, k) + K(j, k))
    R['rel-14 %d%d' % (j, k)] = (K(j, k) + i(k) * 3, i(k) + K(j, k) + i(k) + K(j, k))
    R['rel-15 %d%d' % (j, k)] = (K(j, k) + i(j) + i(k), i(j) + i(k) + K(j, k))
    R['rel-16 %d%d' % (j, k)] = (K(j, k) * 2 + i(j) + i(k), [])
for j, k, l in itertools.combinations(J, 3):
    R['swap-XX %d%d%d' % (j, k, l)] = (X(k, l) + X(j, k), X(j, k) + X(j, l))
    R['swap-XX′ %d%d%d' % (j, k, l)] = (X(j, l) + X(k, l), X(k, l) + X(j, k))
    R['swap-KX %d%d%d' % (j, k, l)] = (K(k, l) + X(j, k), X(j, k) + K(j, l))
    R['swap-KX′ %d%d%d' % (j, k, l)] = (K(j, l) + X(k, l), X(k, l) + K(j, k))
for j, k, l, m in itertools.permutations(J, 4):
    if j < k and l < m and j < l and k < m and k != l:
        R['rel-17 %d%d%d%d' % (j, k, l, m)] = (K(j, k) + K(l, m) + K(j, l) + K(k, m),
                                                K(j, l) + K(k, m) + K(j, k) + K(l, m))


def two_level(g):
    """The 4 × 4 matrix of a two-level generator."""
    import cmath
    M = [[1 if r == c else 0 for c in range(4)] for r in range(4)]
    if g[0] == 'i':
        M[g[1]][g[1]] = 1j
    elif g[0] == 'X':
        a, b = g[1], g[2]
        M[a][a] = M[b][b] = 0
        M[a][b] = M[b][a] = 1
    else:
        a, b = g[1], g[2]
        k = 1 / (1 + 1j)
        M[a][a], M[a][b], M[b][a], M[b][b] = k, k, k, -k
    return M


def circ_matrix(text):
    """The matrix of a circuit, rows and columns indexed 2 x₀ + x₁ (circ's
    bit k is wire k, so index x₀ + 2 x₁ there)."""
    U = circ.unitary(circ.parse(text), 2)
    perm = [0, 2, 1, 3]
    return [[U[perm[r]][perm[c]] for c in range(4)] for r in range(4)]


if __name__ == '__main__':
    bad = 0
    for g in [('i', a) for a in J] + [('X',) + p for p in P] + [('K',) + p for p in P]:
        A, B = two_level(g), circ_matrix(dec([g]))
        if any(abs(A[r][c] - B[r][c]) > 1e-9 for r in range(4) for c in range(4)):
            bad += 1
            print('generator', g)
    for k, (l, r) in R.items():
        if not circ.same(circ.parse(dec(l)), circ.parse(dec(r)), 2):
            bad += 1
            print('FAIL', k)
    print(len(R), 'instances,', bad, 'failures')
