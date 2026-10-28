"""CliffCS₂ on two wires: Bian and Selinger's two-level generators in dimension 4, decoded as
conjugates of three atoms by permutation circuits, and every relation instance carried from one
standard instance per relation by a permutation (`transport`).

Basis index s0 + 2 s1 (wire 0 the least significant bit).  Blocks are named words: the Coxeter
generators s1 = (0 1), s2 = (1 2), s3 = (2 3) of S4 as circuits, the atoms CS (i on index 3), CK
(K on the indices 2, 3) and CX = s3 (X on the indices 2, 3), and single gates."""
import itertools, numpy as np
import cscliff as C
from cscliff import L

H0, H1, S0, S1, CS, SW, W = L('H'), L('H', 1), L('S'), L('S', 1), L('CS'), L('SW'), L('w')
BLK = {
    's1': [H0, S0, S0, CS, CS, H0],     # X on wire 0 when wire 1 is 0
    's2': [SW],
    's3': [H0, CS, CS, H0],             # the CNOT, control wire 1
    'X0': [H0, S0, S0, H0], 'X1': [H1, S1, S1, H1],
    'CK': [S1, S1, S1, CS, H0, CS, H0, CS],
    'CS': [CS], 'w': [W], 'H0': [H0], 'H1': [H1], 'S0': [S0], 'S1': [S1],
}
PERMB = ['s1', 's2', 's3', 'X0', 'X1']
COX = {1: 's1', 2: 's2', 3: 's3'}

def letters(bw):
    out = []
    for b in bw: out += BLK[b]
    return out

def mat(bw): return C.mat(2, letters(bw))

def perm(bw):
    """The permutation (as a tuple p with p[x] the image of x) of a word of permutation blocks."""
    M = mat(bw)
    p = []
    for x in range(4):
        k = int(np.argmax(abs(M[:, x]))); assert abs(abs(M[k, x]) - 1) < 1e-9 and abs(M[k, x] - 1) < 1e-9, (bw, x)
        p.append(k)
    return tuple(p)

PB = {b: perm([b]) for b in PERMB}
assert PB['s1'] == (1, 0, 2, 3) and PB['s2'] == (0, 2, 1, 3) and PB['s3'] == (0, 1, 3, 2)

def compose(ws):
    """The permutation of a time-order word of permutation blocks."""
    p = (0, 1, 2, 3)
    for b in ws: p = tuple(PB[b][p[x]] for x in range(4))
    return p

def shortest(cond, alphabet=PERMB):
    for n in range(0, 6):
        for ws in itertools.product(alphabet, repeat=n):
            if cond(compose(ws)): return list(ws)
    raise Exception('no word')

FRAME = {}
for a in range(4):
    for b in range(a + 1, 4):
        FRAME[(a, b)] = shortest(lambda p: p[2] == a and p[3] == b)
    FRAME[(a,)] = shortest(lambda p: p[3] == a)
ATOM = {'X': 's3', 'K': 'CK', 'i': 'CS'}

def dec(g):
    """A generator ('X', a, b), ('K', a, b), ('i', a) or ('w',) as a block word (time order)."""
    if g[0] == 'w': return ['w']
    F = FRAME[tuple(g[1:])]
    return list(reversed(F)) + [ATOM[g[0]]] + F

def gen_mat(g):
    M = np.eye(4, dtype=complex)
    if g[0] == 'w': return C.w8 * M
    if g[0] == 'i': M[g[1], g[1]] = 1j; return M
    a, b = g[1], g[2]
    U = np.array([[0, 1], [1, 0]]) if g[0] == 'X' else C.w8 ** 7 * C.MH
    M[a, a], M[a, b], M[b, a], M[b, b] = U[0, 0], U[0, 1], U[1, 0], U[1, 1]
    return M

def opw(gs):
    """Generators in the order of matrix multiplication, decoded to a time-order block word."""
    out = []
    for g in reversed(gs): out += dec(g)
    return out

# --- the relations of Figure 1 of Bian and Selinger, as in QCert.BianSelingerUn.Rel
def X(j, k): return ('X', j, k)
def K(j, k): return ('K', j, k)
def I(j): return ('i', j)
REL = {
  'r1': ('j', lambda j: ([I(j)] * 4, [])),
  'r2': ('j<k', lambda j, k: ([X(j, k)] * 2, [])),
  'r3': ('j<k', lambda j, k: ([K(j, k)] * 8, [])),
  'r4': ('j!=k', lambda j, k: ([I(j), I(k)], [I(k), I(j)])),
  'r5': ('k<l j!=k j!=l', lambda j, k, l: ([I(j), X(k, l)], [X(k, l), I(j)])),
  'r6': ('k<l j!=k j!=l', lambda j, k, l: ([I(j), K(k, l)], [K(k, l), I(j)])),
  'r7': ('j<k l<m j!=l j!=m k!=l k!=m', lambda j, k, l, m: ([X(j, k), X(l, m)], [X(l, m), X(j, k)])),
  'r8': ('j<k l<m j!=l j!=m k!=l k!=m', lambda j, k, l, m: ([X(j, k), K(l, m)], [K(l, m), X(j, k)])),
  'r9': ('j<k l<m j!=l j!=m k!=l k!=m', lambda j, k, l, m: ([K(j, k), K(l, m)], [K(l, m), K(j, k)])),
  'r10': ('j<k', lambda j, k: ([I(k), X(j, k)], [X(j, k), I(j)])),
  'r11': ('j<k k<l', lambda j, k, l: ([X(k, l), X(j, k)], [X(j, k), X(j, l)])),
  'r12': ('j<k k<l', lambda j, k, l: ([X(j, l), X(k, l)], [X(k, l), X(j, k)])),
  'r13': ('j<k k<l', lambda j, k, l: ([K(k, l), X(j, k)], [X(j, k), K(j, l)])),
  'r14': ('j<k k<l', lambda j, k, l: ([K(j, l), X(k, l)], [X(k, l), K(j, k)])),
  'r15': ('j<k', lambda j, k: ([K(j, k), I(k), I(k)], [X(j, k), K(j, k)])),
  'r16': ('j<k', lambda j, k: ([K(j, k), I(k), I(k), I(k)], [I(k), K(j, k), I(k), K(j, k)])),
  'r17': ('j<k', lambda j, k: ([K(j, k), I(j), I(k)], [I(j), I(k), K(j, k)])),
  'r18': ('j<k', lambda j, k: ([K(j, k), K(j, k), I(j), I(k)], [])),
  'r19': ('j<k l<m j<l k<m k!=l', lambda j, k, l, m: ([K(j, k), K(l, m), K(j, l), K(k, m)],
                                                       [K(j, l), K(k, m), K(j, k), K(l, m)])),
}

def instances(n=4):
    out = []
    for r, (cond, f) in REL.items():
        nv = f.__code__.co_argcount
        names = 'jklm'[:nv]
        for vals in itertools.product(range(n), repeat=nv):
            env = dict(zip(names, vals))
            ok = True
            for c in cond.split():
                if '!=' in c: a, b = c.split('!='); ok &= env[a] != env[b]
                elif '<' in c: a, b = c.split('<'); ok &= env[a] < env[b]
            if ok:
                l, rr = f(*vals)
                out.append((r, vals, l, rr))
    return out

if __name__ == '__main__':
    for key, F in sorted(FRAME.items()): print(key, F)
    for a in range(4):
        g = ('i', a); assert np.allclose(mat(dec(g)), gen_mat(g)), g
    for a in range(4):
        for b in range(a + 1, 4):
            for t in 'XK':
                g = (t, a, b); assert np.allclose(mat(dec(g)), gen_mat(g)), g
    ins = instances()
    print(len(ins), 'instances')
    for r, vals, l, rr in ins:
        def m(gs):
            M = np.eye(4, dtype=complex)
            for g in gs: M = M @ gen_mat(g)
            return M
        assert np.allclose(m(l), m(rr)), (r, vals)
        assert np.allclose(mat(opw(l)), m(l)) and np.allclose(mat(opw(rr)), m(rr))
    from collections import Counter
    print(Counter(r for r, *_ in ins))
    print('ok')

# --- derivations at the level of blocks
# A step ('rw', p, name, rev) rewrites, at block position p of a time-order block word, one side of
# the block lemma `name` (its left side, or its right side if rev) into the other.
LEM = {
    'U2 c11': (['s1', 's1'], []), 'U2 c22': (['s2', 's2'], []), 'U2 c33': (['s3', 's3'], []),
    'U2 c13': (['s1', 's3'], ['s3', 's1']),
    'U2 b12': (['s1', 's2', 's1'], ['s2', 's1', 's2']), 'U2 b23': (['s2', 's3', 's2'], ['s3', 's2', 's3']),
    'U2 mX0': (['X0'], ['s1', 's3']), 'U2 mX1': (['X1'], ['s2', 'X0', 's2']),
    'U2 i1': (['s1', 'CS'], ['CS', 's1']), 'U2 i2': (['s2', 'CS'], ['CS', 's2']),
    'U2 k1': (['s1', 'CK'], ['CK', 's1']),
}
CANCEL = {'s1': 'U2 c11', 's2': 'U2 c22', 's3': 'U2 c33'}
STAB = {'CK': ['s1'], 'CS': ['s1', 's2'], 's3': ['s1', 's3']}
PASS = {('s1', 'CK'): 'U2 k1', ('s1', 'CS'): 'U2 i1', ('s2', 'CS'): 'U2 i2', ('s1', 's3'): 'U2 c13'}

def apply(W, st):
    _, p, nm, rev = st
    l, r = LEM[nm]
    if rev: l, r = r, l
    assert W[p:p + len(l)] == l, (W, st)
    return W[:p] + r + W[p + len(l):]

def run(W, steps):
    for st in steps: W = apply(W, st)
    return W

def inverse(steps):
    return [(k, p, nm, not rev) for (k, p, nm, rev) in reversed(steps)]

def shift(steps, d):
    return [(k, p + d, nm, rev) for (k, p, nm, rev) in steps]

def inv_perm(p):
    q = [0] * 4
    for x in range(4): q[p[x]] = x
    return tuple(q)

def length(p):
    return sum(1 for a in range(4) for b in range(a + 1, 4) if p[a] > p[b])

def cox_moves(W, deletions=True):
    """Braid moves and (optionally) deletions available in a Coxeter word."""
    out = []
    for p in range(len(W)):
        for nm in ('U2 c13', 'U2 b12', 'U2 b23'):
            l, r = LEM[nm]
            if W[p:p + len(l)] == l: out.append(('rw', p, nm, False))
            if W[p:p + len(r)] == r: out.append(('rw', p, nm, True))
        if deletions and p + 1 < len(W) and W[p] == W[p + 1] and W[p] in CANCEL:
            out.append(('rw', p, CANCEL[W[p]], False))
    return out

def bfs(W, goal, deletions):
    from collections import deque
    start = tuple(W)
    prev = {start: None}
    dq = deque([start])
    while dq:
        x = dq.popleft()
        if goal(list(x)):
            path = []
            while prev[x] is not None:
                y, st = prev[x]; path.append(st); x = y
            return list(reversed(path)), list(x if not path else run(list(start), list(reversed(path))))
        for st in cox_moves(list(x), deletions):
            y = tuple(apply(list(x), st))
            if y not in prev:
                prev[y] = (x, st); dq.append(y)
    raise Exception('no path from %s' % (W,))

def cox_path(u, v):
    """Steps carrying the Coxeter word u to v (the same permutation)."""
    assert compose(u) == compose(v), (u, v)
    n = length(compose(u))
    su, ru = bfs(u, lambda w: len(w) == n, True)
    sv, rv = bfs(v, lambda w: len(w) == n, True)
    sm, _ = bfs(ru, lambda w: w == rv, False)
    steps = su + sm + inverse(sv)
    assert run(list(u), steps) == list(v)
    return steps

def cancel_steps(Q):
    """Steps carrying inv(Q) + Q to the empty word."""
    r = len(Q)
    W = list(reversed(Q)) + list(Q)
    steps = []
    for k in range(r):
        p = r - 1 - k
        steps.append(('rw', p, CANCEL[W[p]], False)); W = apply(W, steps[-1])
    assert W == []
    return steps

def expand(W):
    """Steps replacing every X0, X1 of W by Coxeter words."""
    steps = []
    while True:
        for p, b in enumerate(W):
            if b == 'X1': st = ('rw', p, 'U2 mX1', False); break
            if b == 'X0': st = ('rw', p, 'U2 mX0', False); break
        else:
            return steps, W
        steps.append(st); W = apply(W, st)

def word_for(p, alphabet):
    from collections import deque
    dq = deque([()]); seen = {(0, 1, 2, 3): ()}
    if p == (0, 1, 2, 3): return []
    while dq:
        w = dq.popleft()
        for b in alphabet:
            w2 = w + (b,)
            q = compose(list(w2))
            if q not in seen:
                seen[q] = w2
                if q == p: return list(w2)
                dq.append(w2)
    raise Exception('not in the subgroup: %s %s' % (p, alphabet))

def pure(u, v):
    """Steps from u to v, time-order block words with at most one atom each (CK or CS, the same on
    both sides), everything else permutation blocks."""
    eu, U = expand(list(u)); ev, V = expand(list(v))
    atoms = [b for b in U if b in ('CK', 'CS')]
    assert atoms == [b for b in V if b in ('CK', 'CS')] and len(atoms) <= 1, (u, v)
    if not atoms:
        steps = eu + cox_path(U, V) + inverse(ev)
    else:
        A = atoms[0]
        i, j = U.index(A), V.index(A)
        u1, u2, v1, v2 = U[:i], U[i + 1:], V[:j], V[j + 1:]
        q = tuple(compose(u1)[inv_perm(compose(v1))[x]] for x in range(4))   # π_u1 ∘ π_v1⁻¹
        Q = word_for(q, STAB[A])
        s1 = cox_path(u1, v1 + Q)
        W = v1 + Q + [A] + u2
        mv = []
        for k in reversed(range(len(Q))):
            p = len(v1) + k
            if Q[k] != A: mv.append(('rw', p, PASS[(Q[k], A)], False))
            W = W[:p] + [A, Q[k]] + W[p + 2:]
        s3 = shift(cox_path(Q + u2, v2), len(v1) + 1)
        steps = eu + s1 + mv + s3 + inverse(ev)
    assert run(list(u), steps) == list(v), (u, v)
    return steps

PURE = ['r2', 'r5', 'r7', 'r8', 'r10', 'r11', 'r12', 'r13', 'r14']
STD = {'r1': (3,), 'r3': (2, 3), 'r4': (2, 3), 'r6': (1, 2, 3), 'r9': (0, 1, 2, 3), 'r15': (2, 3),
       'r16': (2, 3), 'r17': (2, 3), 'r18': (2, 3), 'r19': (0, 1, 2, 3)}

def std_sides(r):
    l, rr = REL[r][1](*STD[r])
    return opw(l), opw(rr)

def rename(g, s):
    return (g[0],) + tuple(s[x] for x in g[1:])

def factor_steps(g, g0, P):
    """Steps from dec(g) to inv(P) + dec(g0) + P (the same matrix)."""
    u = dec(g)
    v = list(reversed(P)) + dec(g0) + list(P)
    if g[0] == 'X':
        eu, U = expand(u); ev, V = expand(v)
        steps = eu + cox_path(U, V) + inverse(ev)
        assert run(list(u), steps) == v
        return steps
    return pure(u, v)

def side_steps(gs, gs0, P):
    """Steps from opw(gs) to inv(P) + opw(gs0) + P."""
    W = opw(gs)
    steps = []
    if not gs:
        st = inverse(cancel_steps(list(P)))     # ε -> inv(P) + P
        return st
    off = 0
    for g, g0 in zip(reversed(gs), reversed(gs0)):
        n = len(dec(g))
        fs = shift(factor_steps(g, g0, P), off)
        steps += fs; W = run(W, fs)
        off += len(P) * 2 + len(dec(g0))
    # cancel the junctions P + inv(P)
    k = len(gs)
    for t in range(k - 1, 0, -1):
        # the t-th junction (from the left) sits after t factors
        pos = sum(len(P) * 2 + len(dec(g0)) for g0 in list(reversed(gs0))[:t]) - len(P)
        cs = shift(cancel_steps(list(reversed(P))), pos)
        steps += cs; W = run(W, cs)
    target = list(reversed(P)) + opw(gs0) + list(P)
    assert W == target, (W, target)
    return steps

def transport(r, vals):
    """Steps from opw(lhs) to opw(rhs) of the instance (r, vals), through the standard instance."""
    vals0 = STD[r]
    s = dict(zip(vals0, vals))
    rest = [x for x in range(4) if x not in s]
    free = [y for y in range(4) if y not in s.values()]
    best = None
    for perm_ in itertools.permutations(free):
        s2 = dict(s); s2.update(zip(rest, perm_))
        p = tuple(s2[x] for x in range(4))
        w = word_for(p, ['s1', 's2', 's3'])
        if best is None or len(w) < len(best[1]): best = (s2, w)
    s2, P = best
    l, rr = REL[r][1](*vals)
    l0, r0 = REL[r][1](*vals0)
    assert [rename(g, s2) for g in l0] == l and [rename(g, s2) for g in r0] == rr
    sl = side_steps(l, l0, P)
    sr = side_steps(rr, r0, P)
    name = 'U2 std ' + r
    steps = sl + [('rw', len(P), name, False)] + inverse(sr)
    return steps

def check_transport():
    L0 = dict(LEM)
    for r in STD:
        LEM['U2 std ' + r] = std_sides(r)
    tot = 0
    for r, vals, l, rr in instances():
        if r in STD:
            st = transport(r, vals)
            assert run(opw(l), st) == opw(rr)
            tot += len(st)
    return tot
