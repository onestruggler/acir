# The affine decoding (five-qubit-plan.md, "The decoding from five wires
# on"), checked exactly.
#
#   gadgets   G(V) on n wires: V on wire 0 where every other wire is 0
#             (dec.py's black gadgets between X on the controls), for
#             V in {iZ, XZ, KI = K i_0^-1}
#   alpha     alpha_{p,q} = t_p . L_{p+q}: L_w linear with e_0 -> w (the
#             fan-out F_S from wire 0, S the support of w off wire 0,
#             preceded by CX(j -> 0), j = min supp w, when w_0 = 0), t_p
#             the X's on the bits of p; d(V_(p,q)) = alpha G(V) alpha^-1
#   letters   the P' letters as words of gadgets
#   equivariance  for every letter a (X_v, CX(u -> v)) and w /= 0 the map
#             beta = L_{aw}^-1 a L_w is the claimed word of transvections
#             with controls /= 0
#   classes   Gaussian elimination of up to five distinct points
#
# Maps and words: a word is in operator order (the rightmost letter acts
# first); a linear map is a function on bit tuples.
import sys, os
from itertools import product, permutations, combinations
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from gadgets import (Q, M, ZERO, ONE, I_, MI, NEG, GINV, matrix, relabel, inverse,
                     ctrl_spec, mul2, G_X, G_Z, G_K, G_S)
import dec

# ----------------------------------------------------------------------
# 2 x 2 matrices: {(r, c): v}

def m2(a, b, c, d): return {(0, 0): a, (0, 1): b, (1, 0): c, (1, 1): d}
V_iZ = m2(I_, ZERO, ZERO, MI)
V_XZ = mul2(G_X, G_Z)
V_KI = mul2(G_K, m2(MI, ZERO, ZERO, ONE))        # K . diag(-i, 1) = K_ab i_a^-1
VS = {'iZ': V_iZ, 'XZ': V_XZ, 'KI': V_KI}


def white(n, word):
    negs = [('X', w) for w in range(1, n)]
    return negs + word + negs


def G(n, kind):
    """G(V) on n wires, V on wire 0 where all other wires are 0."""
    if kind == 'iZ': return white(n, dec.G_pp(n))
    if kind == 'XZ': return white(n, dec.G_rot(n))
    if kind == 'KI': return [('X', 0)] + white(n, dec.G_ki(n)) + [('X', 0)]
    raise ValueError(kind)


def two_level(n, V, p, q):
    """V on the basis states p, q (|p> -> V00 |p> + V10 |q>, ...)."""
    d = {x: {x: ONE} for x in product((0, 1), repeat=n)}
    d[p] = {}; d[q] = {}
    for (r, c), v in V.items():
        if v == ZERO: continue
        x, y = (p, q)[r], (p, q)[c]
        d[x][y] = v
    return M(n, d)

# ----------------------------------------------------------------------
# alpha

def bits(n, k): return tuple((k >> i) & 1 for i in range(n))
def add(x, y): return tuple(a ^ b for a, b in zip(x, y))
def e(n, i): return tuple(1 if j == i else 0 for j in range(n))


def F(S):
    """the fan-out from wire 0 onto S."""
    return [('CX', 0, s) for s in S]


def L(n, w):
    """a linear circuit with e_0 -> w (operator order)."""
    S = [i for i in range(1, n) if w[i]]
    if w[0]:
        return F(S)
    j = min(S)
    return [('CX', j, 0)] + F(S)           # F_S first, then CX(j -> 0)


def t(p): return [('X', i) for i in range(len(p)) if p[i]]


def alpha(p, q):
    n = len(p)
    return t(p) + L(n, add(p, q))


def d(n, kind, p, q):
    a = alpha(p, q)
    return a + G(n, kind) + inverse(a)


def act(word, x):
    """the bit map of an affine word."""
    for op in reversed(word):
        x = list(x)
        if op[0] == 'X': x[op[1]] ^= 1
        elif op[0] == 'CX':
            if x[op[1]]: x[op[2]] ^= 1
        else: raise ValueError(op)
        x = tuple(x)
    return x

# ----------------------------------------------------------------------
# The P' letters as words of gadgets (V, p, q), in operator order

def letter(kind, *ix):
    if kind == 'pp':
        a, b = ix
        return [] if a == b else [('iZ', a, b)]
    if kind == 'px':
        c, a, b = ix
        if c == a: return [('XZ', a, b)]
        if c == b: return [('XZ', b, a)]
        return [('iZ', c, a), ('iZ', c, a), ('XZ', a, b)]
    if kind == 'dx':
        a, b, c, dd = ix
        return letter('px', a, a, b) + letter('px', b, c, dd)
    if kind == 'ki':
        a, b, s = ix
        return [('KI', a, b)] + ([] if s == a else [('iZ', a, s)])
    raise ValueError(kind)


def letter_matrix(n, kind, *ix):
    """the letter's matrix (asG: written-order product of two-level
    letters i_[a], X_[a,b], K_[a,b])."""
    I = M.ident(n)
    def ph(a, v):
        dd = {x: {x: ONE} for x in product((0, 1), repeat=n)}; dd[a] = {a: v}; return M(n, dd)
    def X(a, b): return two_level(n, G_X, a, b)
    def K(a, b): return two_level(n, G_K, a, b)
    if kind == 'pp':
        a, b = ix; return ph(a, I_) * ph(b, MI)
    if kind == 'px':
        c, a, b = ix; return ph(c, NEG) * X(a, b)
    if kind == 'dx':
        a, b, c, dd = ix; return X(a, b) * X(c, dd)
    if kind == 'ki':
        a, b, s = ix; return K(a, b) * ph(s, MI)


def gw_matrix(n, gw, cache):
    R = M.ident(n)
    for (kind, p, q) in gw:
        key = (kind, p, q)
        if key not in cache: cache[key] = matrix(n, d(n, kind, p, q))
        R = R * cache[key]
    return R

# ----------------------------------------------------------------------
# Checks

def check_gadgets(n):
    for kind, V in VS.items():
        got = matrix(n, G(n, kind))
        want = ctrl_spec(n, 0, list(range(1, n)), V, neg=tuple(range(1, n)))
        assert got == want, (n, kind)
    print(f'gadgets ok on {n} wires: G(iZ), G(XZ), G(KI)')


def check_alpha(n):
    z = tuple(0 for _ in range(n))
    cache = {}
    cnt = 0
    for p in product((0, 1), repeat=n):
        for q in product((0, 1), repeat=n):
            if p == q: continue
            a = alpha(p, q)
            assert act(a, z) == p and act(a, e(n, 0)) == q, (p, q)
            for kind, V in VS.items():
                assert matrix(n, d(n, kind, p, q)) == two_level(n, V, p, q), (kind, p, q)
                cnt += 1
    print(f'alpha ok on {n} wires: {cnt} decoded gadgets are their two-level matrices')


def check_letters(n, sample=None):
    pts = list(product((0, 1), repeat=n))
    order = {x: i for i, x in enumerate(pts)}
    cache = {}
    cnt = 0
    for a, b in permutations(pts, 2):
        assert gw_matrix(n, letter('pp', a, b), cache) == letter_matrix(n, 'pp', a, b)
        cnt += 1
    for a, b in permutations(pts, 2):
        if order[a] > order[b]: continue
        for c in pts:
            assert gw_matrix(n, letter('px', c, a, b), cache) == letter_matrix(n, 'px', c, a, b), (c, a, b)
            cnt += 1
        for s in pts:
            assert gw_matrix(n, letter('ki', a, b, s), cache) == letter_matrix(n, 'ki', a, b, s), (a, b, s)
            cnt += 1
    pairs = [(a, b) for a, b in permutations(pts, 2) if order[a] < order[b]]
    import random
    rnd = random.Random(1)
    sel = [(x, y) for x in pairs for y in pairs]
    if sample: sel = rnd.sample(sel, sample)
    for (a, b), (c, dd) in sel:
        assert gw_matrix(n, letter('dx', a, b, c, dd), cache) == letter_matrix(n, 'dx', a, b, c, dd), (a, b, c, dd)
        cnt += 1
    print(f'letters ok on {n} wires: {cnt} letters')

# ---------------------------------------------------------------- equivariance

def T(u, v): return ('CX', u, v)
def SW(u, j): return [T(u, j), T(j, u), T(u, j)]


# The generic lemmas (F_R a fan-out from wire 0, an involution):
#   fan-com  u not in R, u, v /= 0:   F_R T(u,v) F_R = T(u,v)
#   fan-in   u in R, v /= 0, u:       F_R T(u,v) F_R = T(u,v) T(0,v)
#   fan-0    u not in R, u /= 0:      F_R T(u,0) F_R = T(u,0) prod_{s in R} T(u,s)
#   pivot    u /= j in R:             F_R T(u,0) T(j,0) F_R
#                                     = SW(u,j) fan0(u, R') fan0(j, R'), R' = R - {u,j}
def fan0(u, R): return [T(u, 0)] + [T(u, s) for s in R]


def pivot(u, j, R):
    """F_R T(u,0) T(j,0) F_R for u /= j both in R."""
    if u == j: return []
    R2 = [s for s in R if s not in (u, j)]
    return SW(u, j) + fan0(u, R2) + fan0(j, R2)


def beta_claim(n, a, w):
    """the claimed word for L_{aw}^-1 a L_w (a = CX(u -> v)), all
    controls /= 0."""
    _, u, v = a
    S = [i for i in range(1, n) if w[i]]
    aw = act([a], w)
    S2 = [i for i in range(1, n) if aw[i]]
    if w[0]:
        if u != 0 and v != 0: return [T(u, v)]                 # A1
        if u == 0: return []                                   # A2
        if u not in S: return fan0(u, S)                       # A3
        return pivot(min(S), u, S)                             # A3, u in S: L_aw = T(j,0) F_S
    j = min(S)
    if u != 0 and v != 0:                                      # B1
        if u not in S:
            return [T(u, v)] if v != j else fan0(u, [s for s in S if s != j])
        if v != j:
            j2 = min(S2)
            return pivot(j2, j, S2) + [T(u, v)]
        # v = j: a L_w = T(u,0) T(j,0) F_{S'} T(u,j), S' = S - {j}
        j2 = min(S2)
        return pivot(j2, u, S2) + fan0(j, S2) + [T(u, j)]
    if u == 0:                                                 # B2
        if v != j: return [T(j, v)]
        return fan0(j, [s for s in S if s != j])
    # B3: v = 0
    if u not in S: return fan0(u, S)
    return pivot(u, j, S)


def check_beta(n):
    covered = missing = 0
    for w in product((0, 1), repeat=n):
        if not any(w): continue
        for u in range(n):
            for v in range(n):
                if u == v: continue
                a = T(u, v)
                aw = act([a], w)
                beta = inverse(L(n, aw)) + [a] + L(n, w)
                claim = beta_claim(n, a, w)
                for x in product((0, 1), repeat=n):
                    pass
                if claim is None:
                    missing += 1
                    continue
                assert all(g[1] != 0 for g in claim), (a, w, claim)
                for x in product((0, 1), repeat=n):
                    assert act(beta, x) == act(claim, x), (a, w, claim)
                covered += 1
    print(f'beta on {n} wires: {covered} cases as claimed, {missing} not yet covered')


# ---------------------------------------------------------------- the axioms
def check_axioms(n=5):
    from itertools import permutations as P
    def same(l, r):
        return all(act(l, x) == act(r, x) for x in product((0, 1), repeat=n))
    X_ = lambda v: ('X', v)
    for u, v in P(range(n), 2):
        assert same([T(u, v), T(u, v)], [])
        assert same([T(u, v), X_(u)], [X_(u), X_(v), T(u, v)])          # x-ctl
        assert same([T(u, v), X_(v)], [X_(v), T(u, v)])                 # x-tgt
        assert same([T(u, v), T(v, u), T(u, v)], [T(v, u), T(u, v), T(v, u)])   # t-sw
    for x, y, z in P(range(n), 3):
        assert same([T(x, y), T(y, z), T(x, y)], [T(y, z), T(x, z)])    # t-ts
        assert same([T(y, z), T(x, y), T(y, z)], [T(x, y), T(x, z)])    # t-st
        assert same([T(x, y), T(x, z)], [T(x, z), T(x, y)])             # t-cc
        assert same([T(x, z), T(y, z)], [T(y, z), T(x, z)])             # t-tt
        assert same([T(x, y), X_(z)], [X_(z), T(x, y)])                 # x-far
        o, u, j = x, y, z                                               # t-pv
        assert same([T(j, o), T(u, o), T(o, u), T(o, j)],
                    [T(o, u), T(o, j)] + SW(u, j) + [T(u, o), T(j, o)])
    for a, b, c, d in P(range(n), 4):
        assert same([T(a, b), T(c, d)], [T(c, d), T(a, b)])             # t-dd
    print('axioms ok on', n, 'wires')
if __name__ == '__main__':
    what = sys.argv[1:] or ["gadgets", "alpha", "letters", "beta", "axioms"]
    if "axioms" in what: check_axioms(5)
    if 'gadgets' in what:
        check_gadgets(4); check_gadgets(5)
    if 'alpha' in what:
        check_alpha(4)
    if 'letters' in what:
        check_letters(4, sample=3000)
    if 'beta' in what:
        check_beta(4); check_beta(5); check_beta(6)


