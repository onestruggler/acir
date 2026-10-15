# Does the hybrid's controlled branch L_23(kappa_0) (three qubits, wires
# 0 2 3, the branch where wire 1 is set) factor into pieces whose
# wire-1-controlled versions are circuits?  Pieces: one-qubit S, K (lift
# CS(1,x), CK(1,x)), CX, CZ (lift Toffoli, CCZ), the phase i (lift S_1),
# and the contents L_xy(q_v) of the phase gadgets (q in Q8; lift: a phase
# gadget black on wire 1).  Meet in the middle on 8 x 8 matrices.
import itertools, sys
I = 1j; g = 1 / (1 + I)
W = (0, 2, 3)                      # the branch's wires, as matrix qubits 0 1 2
def idx(w): return W.index(w)
def kron_apply(M1, q):
    """the 8x8 matrix of the one-qubit M1 on qubit q."""
    out = [[0] * 8 for _ in range(8)]
    for r in range(8):
        for c in range(8):
            if all(((r >> k) & 1) == ((c >> k) & 1) for k in range(3) if k != q):
                out[r][c] = M1[(r >> q) & 1][(c >> q) & 1]
    return out
def diag8(f): return [[f(r) if r == c else 0 for c in range(8)] for r in range(8)]
def perm8(f): return [[1 if r == f(c) else 0 for c in range(8)] for r in range(8)]
def mm(A, B): return [[sum(A[r][k] * B[k][c] for k in range(8) if A[r][k] != 0) for c in range(8)] for r in range(8)]
def key(A): return tuple(complex(round(x.real, 6), round(x.imag, 6)) for r in A for x in r)
S1 = [[1, 0], [0, I]]; Sd1 = [[1, 0], [0, -I]]; K1 = [[g, g], [g, -g]]; Kd1 = [[g.conjugate(), g.conjugate()], [g.conjugate(), -g.conjugate()]]
X1 = [[0, 1], [1, 0]]; Z1 = [[1, 0], [0, -1]]; Y1 = [[0, -I], [I, 0]]
gens = {}
for w in W:
    q = idx(w)
    for nm, M in (('S', S1), ('Sd', Sd1), ('K', K1), ('Kd', Kd1)): gens[f'{nm}{w}'] = kron_apply(M, q)
for a, b in itertools.permutations(W, 2):
    qa, qb = idx(a), idx(b)
    gens[f'CX{a}{b}'] = perm8(lambda c, qa=qa, qb=qb: c ^ (1 << qb) if (c >> qa) & 1 else c)
for a, b in itertools.combinations(W, 2):
    qa, qb = idx(a), idx(b)
    gens[f'CZ{a}{b}'] = diag8(lambda r, qa=qa, qb=qb: -1 if (r >> qa) & 1 and (r >> qb) & 1 else 1)
gens['i'] = diag8(lambda r: I)
# gadget contents L_xy(q_v)
for v in W:
    x, y = [w for w in W if w != v]
    qx, qy, qv = idx(x), idx(y), idx(v)
    for qn, Q in (('iZ', [[I, 0], [0, -I]]), ('-iZ', [[-I, 0], [0, I]]), ('iX', [[0, I], [I, 0]]),
                  ('-iX', [[0, -I], [-I, 0]]), ('iY', [[0, 1], [-1, 0]]), ('-iY', [[0, -1], [1, 0]])):
        M = [[0] * 8 for _ in range(8)]
        for r in range(8):
            for c in range(8):
                same = all(((r >> k) & 1) == ((c >> k) & 1) for k in range(3) if k != qv)
                if not same: continue
                if (c >> qx) & 1 and (c >> qy) & 1: M[r][c] = Q[(r >> qv) & 1][(c >> qv) & 1]
                else: M[r][c] = 1 if r == c else 0
        gens[f'L{x}{y}({qn}){v}'] = M
names = list(gens)
print(len(names), 'generators')
# the target: L_23(kappa_0), kappa = [V^2, K], V = S S K S
def m2(A, B): return [[sum(A[r][k] * B[k][c] for k in range(2)) for c in range(2)] for r in range(2)]
def w2(s):
    M = [[1, 0], [0, 1]]
    for ch in s: M = m2(M, {'S': S1, 'K': K1, 's': Sd1, 'k': Kd1}[ch])
    return M
V = w2('SSKS'); V2 = m2(V, V); kap = m2(m2(V2, K1), m2(m2(m2(V2, V2), V2) if False else w2('sksskssk') if False else None, None)) if False else None
# kappa = V^2 K V^-2 K^-1
def inv2(A):
    d = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    return [[A[1][1] / d, -A[0][1] / d], [-A[1][0] / d, A[0][0] / d]]
kap = m2(m2(V2, K1), m2(inv2(V2), inv2(K1)))
T = [[0] * 8 for _ in range(8)]
q2, q3, q0 = idx(2), idx(3), idx(0)
for r in range(8):
    for c in range(8):
        same = all(((r >> k) & 1) == ((c >> k) & 1) for k in range(3) if k != q0)
        if not same: continue
        if (c >> q2) & 1 and (c >> q3) & 1: T[r][c] = kap[(r >> q0) & 1][(c >> q0) & 1]
        else: T[r][c] = 1 if r == c else 0
D = int(sys.argv[1]) if len(sys.argv) > 1 else 3
E = [[1 if r == c else 0 for c in range(8)] for r in range(8)]
# left: words of length <= D from E; right: T times inverses
def layer(start, D, right=False):
    seen = {key(start): (start, [])}; fr = [(start, [])]
    for _ in range(D):
        nf = []
        for (A, w) in fr:
            for n in names:
                B = mm(A, gens[n])
                k = key(B)
                if k not in seen: seen[k] = (B, w + [n]); nf.append((B, w + [n]))
        fr = nf
        print('  layer size', len(seen), flush=True)
    return seen
left = layer(E, D)
# a word w with w = T: T = L R  <=>  T R^-1 = L ; search R^-1 as words applied to T from the right
def inv8(A):
    return [[A[c][r].conjugate() for c in range(8)] for r in range(8)]     # unitary
ginv = {n: inv8(M) for n, M in gens.items()}
seen = {key(T): (T, [])}; fr = [(T, [])]
found = None
for d in range(D + 1):
    for (A, w) in fr:
        if key(A) in left:
            found = (left[key(A)][1], list(reversed(w))); break
    if found or d == D: break
    nf = []
    for (A, w) in fr:
        for n in names:
            B = mm(A, ginv[n]); k = key(B)
            if k not in seen: seen[k] = (B, w + [n]); nf.append((B, w + [n]))
    fr = nf
    print('  right layer', len(seen), flush=True)
print('found:', found)
