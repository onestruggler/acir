# Constructions for the decoding from four wires on, checked exactly.
#
# The letters of P' decode to multi-controlled gates, and no
# multi-controlled phase gate with every other wire controlling is a
# circuit on its own (det i); the det-1 combinations are.  tBox.py
# found that Clement's box recursion does not carry over to an iZ-box.
# What does: two commutator identities and a borrowed-wire recursion.
#
#   [X, S]          = X S X S^-1 = iZ,
#   [K, Z]          = K Z K^-1 Z = X Z,
#   [L_{C2+a}(S_t), L_{C1}(X_a)] = L_C(S_t^3 CZ_{a t})     (C = C1 + C2, a off C, t)
#   [L_{C2+a}(K_t), L_{C1}(X_a)] = L_C(K_t) . L_C(i on a = 0)
#
# so with Barenco's split-control trick L_{C1+C2}([V, W]) =
# L_{C1}(V) L_{C2}(W) L_{C1}(V^-1) L_{C2}(W^-1):
#
#   (1) L^m(S_t)^3 = [L_{C2+a}(S_t), L_{C1}(X_a)] . L_{C+a}(Z_t), |C1| = 2:
#       multi-controlled S with two idle wires, from one with fewer
#       controls, a multi-controlled X and a box;
#   (2) L^m(K_t)   = [L_{C2+a}(K_t), L_{C1}(X_a)] . X_a L^m(S_a)^3 X_a:
#       multi-controlled K with two idle wires, likewise;
#   (3) L^{n-1}(iZ_t) = L_{C1}(X_t) L_{C2}(S_t) L_{C1}(X_t) L_{C2}(S_t)^3,
#       |C1| = 2: the consecutive phase pair pp a b;
#   (4) L^{n-1}(XZ_t) = [L_c(K_t), L_{C2}(Z_t)]: the rotation, (-1)_a X_ab;
#   (5) [L_{C2+a}(K_t), L_{C1}(X_a)] = K_{rs} K_{pq}^-1, the pairs at
#       a = 1 and a = 0: a K pair;
#   (6) L^{n-2}(G) for a 2-qubit G with det 1, from [V, W] = G:
#       the hybrid ki a b s at a sink one wire-flip away.
# Multi-controlled X is K box K^-1 and the box is Clement's.
# Exact arithmetic: Gaussian rationals.
import sys
from fractions import Fraction as F
from itertools import product

class Q:
    __slots__ = ('r', 'i')
    def __init__(self, r, i=0):
        self.r = F(r); self.i = F(i)
    def __add__(s, o): return Q(s.r + o.r, s.i + o.i)
    def __sub__(s, o): return Q(s.r - o.r, s.i - o.i)
    def __mul__(s, o): return Q(s.r * o.r - s.i * o.i, s.r * o.i + s.i * o.r)
    def __eq__(s, o): return s.r == o.r and s.i == o.i
    def __hash__(s): return hash((s.r, s.i))
    def __repr__(s): return f'({s.r}+{s.i}i)'

ZERO, ONE, I_ = Q(0), Q(1), Q(0, 1)
MI = Q(0, -1); NEG = Q(-1)
GINV = Q(F(1, 2), F(-1, 2))          # 1/(1+i)

# 2x2 and 4x4 gates as dicts (row, col) -> Q over bit tuples.
def mat2(rows):
    return {(r, c): rows[r][c] for r in range(2) for c in range(2)}
S2  = mat2([[ONE, ZERO], [ZERO, I_]])
Z2  = mat2([[ONE, ZERO], [ZERO, NEG]])
X2  = mat2([[ZERO, ONE], [ONE, ZERO]])
K2  = mat2([[GINV, GINV], [GINV, GINV * NEG]])
IZ2 = mat2([[I_, ZERO], [ZERO, MI]])
def mm2(A, B):
    return {(r, c): sum((A[(r, k)] * B[(k, c)] for k in range(2)), ZERO) for r in range(2) for c in range(2)}
def inv2(A):   # unitary: conjugate transpose
    return {(r, c): Q(A[(c, r)].r, -A[(c, r)].i) for r in range(2) for c in range(2)}
XZ2 = mm2(X2, Z2)
S3 = mm2(S2, mm2(S2, S2))

n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
N = 2 ** n
STATES = list(product((0, 1), repeat=n))

class M:
    """Sparse-ish N x N matrix over Q, as dict of dicts: row -> {col: val}."""
    def __init__(self, d): self.d = d
    @staticmethod
    def ident():
        return M({x: {x: ONE} for x in STATES})
    def __mul__(A, B):
        out = {}
        for x, row in A.d.items():
            acc = {}
            for y, a in row.items():
                for z, b in B.d.get(y, {}).items():
                    acc[z] = acc.get(z, ZERO) + a * b
            out[x] = {z: v for z, v in acc.items() if v != ZERO}
        return M(out)
    def __eq__(A, B): return A.d == B.d
    def inv(A):
        out = {}
        for x, row in A.d.items():
            for y, v in row.items():
                out.setdefault(y, {})[x] = Q(v.r, -v.i)
        return M(out)
    def __pow__(A, k):
        R = M.ident()
        for _ in range(k): R = R * A
        return R

def ctrl(C, T, G, neg=()):
    """Lambda_C(G on wires T): G a 2^|T| gate dict over bit tuples; the
    controls in C set (those in neg clear)."""
    out = {}
    for x in STATES:
        active = all((x[c] == 0) if c in neg else (x[c] == 1) for c in C)
        if not active:
            out[x] = {x: ONE}
            continue
        row = {}
        tb = tuple(x[t] for t in T)
        for cb in product((0, 1), repeat=len(T)):
            v = G[(tb, cb)] if len(T) > 1 else G[(tb[0], cb[0])]
            if v == ZERO: continue
            y = list(x)
            for t, b in zip(T, cb): y[t] = b
            row[tuple(y)] = v
        out[x] = row
    return M(out)

def phase_on(pred, ph):
    """diag: ph where pred(x), else 1."""
    return M({x: {x: ph if pred(x) else ONE} for x in STATES})

def comm(A, B): return A * B * A.inv() * B.inv()

def check(name, ok):
    print(('ok   ' if ok else 'FAIL ') + name, flush=True)
    return ok

allok = True
W = list(range(n))

# (1) multi-controlled S: L^m(S_t)^3 = [L_{C2+a}(S_t), L_{C1}(X_a)] . L_{C+a}(Z_t)
for m in range(2, n - 2):              # two idle wires: m <= n - 3
    t, a = 0, 1
    C = W[2:2 + m]; C1, C2 = C[:2], C[2:]
    lhs = ctrl(C, [t], S2) ** 3
    rhs = comm(ctrl(C2 + [a], [t], S2), ctrl(C1, [a], X2)) * ctrl(C + [a], [t], Z2)
    allok &= check(f'(1) L^{m}(S) via borrowed wire, n={n}', lhs == rhs)

# (2) multi-controlled K: L^m(K_t) = [L_{C2+a}(K_t), L_{C1}(X_a)] . X_a L_C(S_a)^3 X_a
for m in range(2, n - 2):
    t, a = 0, 1
    C = W[2:2 + m]; C1, C2 = C[:2], C[2:]
    lhs = ctrl(C, [t], K2)
    Xa = ctrl([], [a], X2)
    rhs = comm(ctrl(C2 + [a], [t], K2), ctrl(C1, [a], X2)) * Xa * (ctrl(C, [a], S2) ** 3) * Xa
    allok &= check(f'(2) L^{m}(K) via borrowed wire, n={n}', lhs == rhs)

# (3) the consecutive phase pair: L^{n-1}(iZ_t) = L_{C1}(X_t) L_{C2}(S_t) L_{C1}(X_t) L_{C2}(S_t)^3
t = 0; C = W[1:]; C1, C2 = C[:2], C[2:]
lhs = ctrl(C, [t], IZ2)
rhs = ctrl(C1, [t], X2) * ctrl(C2, [t], S2) * ctrl(C1, [t], X2) * (ctrl(C2, [t], S2) ** 3)
allok &= check(f'(3) L^{n-1}(iZ) = [L(X), L(S)], n={n}', lhs == rhs)
# and it is the phase pair i_a i_b^-1 on the two states with C set
pp = phase_on(lambda x: all(x[c] for c in C) and x[t] == 0, I_) * \
     phase_on(lambda x: all(x[c] for c in C) and x[t] == 1, MI)
allok &= check(f'(3) ... which is pp on consecutive states, n={n}', lhs == pp)

# (4) the rotation: L^{n-1}(XZ_t) = [L_c(K_t), L_{C2}(Z_t)]
t, c = 0, 1; C2 = W[2:]
lhs = ctrl(W[1:], [t], XZ2)
rhs = comm(ctrl([c], [t], K2), ctrl(C2, [t], Z2))
allok &= check(f'(4) L^{n-1}(XZ) = [CK, box], n={n}', lhs == rhs)

# (5) a K pair: [L_{C2+a}(K_t), L_{C1}(X_a)] with C = all but t, a
t, a = 0, 1; C = W[2:]; C1, C2 = C[:2], C[2:]
lhs = comm(ctrl(C2 + [a], [t], K2), ctrl(C1, [a], X2))
Kpair_a1 = ctrl(C + [a], [t], K2)                         # K on the pair at a = 1
Kpair_a0 = ctrl(C + [a], [t], K2, neg=(a,)).inv()          # K^-1 on the pair at a = 0
allok &= check(f'(5) [L(K), L(X)] = K_(a=1) K_(a=0)^-1, n={n}', lhs == Kpair_a1 * Kpair_a0)

# (6) the hybrid at a sink one flip away: G = L_{u=1}(K_w) . (-i at u=0, w=0)
#     on wires (u, w); G has det 1; find V, W in the 2-qubit group with
#     [V, W] = G by a small search, then L_C(G) = L_{C1}(V) L_{C2}(W) ...
def g4(rows):
    bits = [(0, 0), (0, 1), (1, 0), (1, 1)]
    return {(bits[r], bits[c]): rows[r][c] for r in range(4) for c in range(4)}
Z4 = [[ZERO] * 4 for _ in range(4)]
Grows = [[ONE, ZERO, ZERO, ZERO], [ZERO, MI, ZERO, ZERO],
         [ZERO, ZERO, GINV, GINV], [ZERO, ZERO, GINV, GINV * NEG]]
# order (u, w): 00 -> 1 ; 01 -> ? we want -i at (u=0, w=0): fix below
Grows = [[MI, ZERO, ZERO, ZERO], [ZERO, ONE, ZERO, ZERO],
         [ZERO, ZERO, GINV, GINV], [ZERO, ZERO, GINV, GINV * NEG]]
G = g4(Grows)
u, w = 0, 1
Gm = ctrl([], [u, w], G)
# direct: K on the pair (u=1), -i at (u=0,w=0)
direct = ctrl([u], [w], K2) * phase_on(lambda x: x[u] == 0 and x[w] == 0, MI)
allok &= check('(6) G = L_u(K_w) . (-i at u=0,w=0) assembled', Gm == direct)

# 2-qubit generators on (u, w) and a breadth-first commutator search
two = {
    'S0': ctrl([], [u], S2), 'S1': ctrl([], [w], S2),
    'K0': ctrl([], [u], K2), 'K1': ctrl([], [w], K2),
    'CS': ctrl([u], [w], S2),
    'X0': ctrl([], [u], X2), 'X1': ctrl([], [w], X2),
    'CX01': ctrl([u], [w], X2), 'CX10': ctrl([w], [u], X2),
}
def words(depth):
    frontier = [((), M.ident())]
    seen = {}
    for _ in range(depth):
        nxt = []
        for wd, Mx in frontier:
            for g, Mg in two.items():
                Mn = Mx * Mg
                key = tuple(sorted((x, tuple(sorted(r.items(), key=repr))) for x, r in Mn.d.items()))
                if key in seen: continue
                seen[key] = wd + (g,)
                nxt.append((wd + (g,), Mn))
        frontier = nxt
    return seen

if n == 4:
    pool = words(4)
    mats = {}
    for key, wd in pool.items():
        Mx = M.ident()
        for g in wd: Mx = Mx * two[g]
        mats[wd] = Mx
    found = None
    items = list(mats.items())
    for wV, V in items:
        Vi = V.inv()
        for wW, Wm in items:
            if V * Wm * Vi * Wm.inv() == Gm:
                found = (wV, wW); break
        if found: break
    print('(6) [V, W] = G with V, W of length <= 4:', found, flush=True)
    if found:
        wV, wW = found
        V, Wm = mats[wV], mats[wW]
        # L_C(G) = L_{C1}(V) L_{C2}(W) L_{C1}(V^-1) L_{C2}(W^-1) on n wires, C = all but u, w
        C = W[2:]; C1, C2 = C[:1], C[1:]
        lhs = ctrl(C, [u, w], G)
        rhs = ctrl(C1, [u, w], {k: v for k, v in zip(G.keys(), G.values())})  # placeholder
        # build L_{C1}(V) by applying V's 4x4 under control
        def as4(Mx):
            bits = [(0, 0), (0, 1), (1, 0), (1, 1)]
            d = {}
            for rb in bits:
                x = [0] * n; x[u], x[w] = rb
                row = Mx.d[tuple(x)]
                for cb in bits:
                    y = [0] * n; y[u], y[w] = cb
                    d[(rb, cb)] = row.get(tuple(y), ZERO)
            return d
        V4, W4 = as4(V), as4(Wm)
        rhs = ctrl(C1, [u, w], V4) * ctrl(C2, [u, w], W4) * ctrl(C1, [u, w], as4(V.inv())) * ctrl(C2, [u, w], as4(Wm.inv()))
        allok &= check(f'(6) L^{n-2}(G) by split-control commutator, n={n}', lhs == rhs)

print('ALL OK' if allok else 'SOME FAILED')
