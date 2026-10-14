# The decoding's gadgets as circuits, checked exactly.
#
# Words are lists of gate applications on wires, in word order (the
# rightmost gate acts first, as ⟦ w • v ⟧ = ⟦ w ⟧ · ⟦ v ⟧).  The gates are
# the generators iI, S, K, CS and the shortcuts of Syntactics/TwoQubit
# (X, Z, CX, SWAP, CK), applied directly; relabelling a word's wires
# stands for conjugation by a swap network.
#
#   box k      Clement's dashed box: -1 iff wires 1..k set, wire 0 idle
#   rotXZ k    XZ on wire 0 iff wires 1..k set:  [CK, Ex<box k>]
#   cX k       X on wire 0 iff wires 2..k+1 set, wire 1 idle: K box K^-1
#
# and the search for the letters' 1-qubit cores as commutators of
# "cheap" elements — reflections U Z U^-1 and rotations U XZ U^-1 of the
# 1-qubit Clifford group, whose multi-controlled versions are U box U^-1
# and U rotXZ U^-1, needing one idle wire.
import sys
from fractions import Fraction as F
from itertools import product, permutations

class Q:
    __slots__ = ('r', 'i')
    def __init__(self, r, i=0): self.r = F(r); self.i = F(i)
    def __add__(s, o): return Q(s.r + o.r, s.i + o.i)
    def __sub__(s, o): return Q(s.r - o.r, s.i - o.i)
    def __mul__(s, o): return Q(s.r * o.r - s.i * o.i, s.r * o.i + s.i * o.r)
    def __neg__(s): return Q(-s.r, -s.i)
    def __eq__(s, o): return s.r == o.r and s.i == o.i
    def __hash__(s): return hash((s.r, s.i))
    def __repr__(s): return f'({s.r}+{s.i}i)'
    def conj(s): return Q(s.r, -s.i)

ZERO, ONE, I_, MI, NEG = Q(0), Q(1), Q(0, 1), Q(0, -1), Q(-1)
GINV = Q(F(1, 2), F(-1, 2))

# ----------------------------------------------------------------------
# Matrices over basis states

class M:
    def __init__(self, n, d): self.n = n; self.d = d      # d : row -> {col: val}
    @staticmethod
    def ident(n):
        return M(n, {x: {x: ONE} for x in product((0, 1), repeat=n)})
    def __mul__(A, B):
        out = {}
        for x, row in A.d.items():
            acc = {}
            for y, a in row.items():
                for z, b in B.d.get(y, {}).items():
                    acc[z] = acc.get(z, ZERO) + a * b
            out[x] = {z: v for z, v in acc.items() if v != ZERO}
        return M(A.n, out)
    def __eq__(A, B): return A.d == B.d
    def inv(A):      # unitary
        out = {}
        for x, row in A.d.items():
            for y, v in row.items():
                out.setdefault(y, {})[x] = v.conj()
        return M(A.n, out)
    def __pow__(A, k):
        R = M.ident(A.n)
        for _ in range(k): R = R * A
        return R
    def entry(A, x, y): return A.d.get(x, {}).get(y, ZERO)

def commutator(A, B): return A * B * A.inv() * B.inv()

# ----------------------------------------------------------------------
# Gates on wires

def apply_gate(op, col):
    """col: {state: coef}; returns the new column after one gate."""
    kind = op[0]
    out = {}
    def add(x, v):
        if v == ZERO: return
        out[x] = out.get(x, ZERO) + v
    for x, c in col.items():
        if kind == 'iI':
            add(x, c * I_)
        elif kind == 'S':
            add(x, c * I_ if x[op[1]] else c)
        elif kind == 'Z':
            add(x, -c if x[op[1]] else c)
        elif kind == 'X':
            y = list(x); y[op[1]] ^= 1; add(tuple(y), c)
        elif kind == 'K':
            w = op[1]
            y0 = list(x); y0[w] = 0; y1 = list(x); y1[w] = 1
            add(tuple(y0), c * GINV)
            add(tuple(y1), c * GINV * (NEG if x[w] else ONE))
        elif kind == 'CS':
            add(x, c * I_ if (x[op[1]] and x[op[2]]) else c)
        elif kind == 'CX':
            if x[op[1]]:
                y = list(x); y[op[2]] ^= 1; add(tuple(y), c)
            else: add(x, c)
        elif kind == 'SWAP':
            y = list(x); y[op[1]], y[op[2]] = y[op[2]], y[op[1]]; add(tuple(y), c)
        elif kind == 'CK':
            cw, t = op[1], op[2]
            if x[cw]:
                y0 = list(x); y0[t] = 0; y1 = list(x); y1[t] = 1
                add(tuple(y0), c * GINV)
                add(tuple(y1), c * GINV * (NEG if x[t] else ONE))
            else: add(x, c)
        else:
            raise ValueError(op)
    return {k: v for k, v in out.items() if v != ZERO}

def matrix(n, word):
    d = {}
    for y in product((0, 1), repeat=n):
        col = {y: ONE}
        for op in reversed(word):
            col = apply_gate(op, col)
        for x, v in col.items():
            d.setdefault(x, {})[y] = v
    return M(n, d)

def relabel(word, pi):
    return [(op[0],) + tuple(pi.get(w, w) for w in op[1:]) for op in word]

def up(word): return relabel(word, {w: w + 1 for w in range(64)})

def inverse(word):
    """The inverse word: each gate inverted."""
    inv = []
    for op in reversed(word):
        k = op[0]
        if k == 'iI': inv += [op] * 3
        elif k == 'S': inv += [op] * 3
        elif k == 'CS': inv += [op] * 3
        elif k == 'K': inv += [op, ('iI',)]           # K^-1 = i K
        elif k == 'CK': inv += [('S', op[1]), op]     # Lambda(K)^-1 = Lambda(iK) = S_c Lambda(K)
        else: inv += [op]                              # involutions
    return inv

# ----------------------------------------------------------------------
# Specifications: controlled operators

def ctrl_spec(n, t, controls, G2, neg=()):
    """Lambda_controls(G on wire t); G2 a 2x2 over {(0,0),(0,1),(1,0),(1,1)}:
    G2[(r,c)] the entry; controls set (or clear, for those in neg)."""
    d = {}
    for y in product((0, 1), repeat=n):
        active = all((y[c] == 0) if c in neg else (y[c] == 1) for c in controls)
        if not active:
            d.setdefault(y, {})[y] = ONE; continue
        for r in (0, 1):
            v = G2[(r, y[t])]
            if v == ZERO: continue
            x = list(y); x[t] = r
            d.setdefault(tuple(x), {})[y] = v
    return M(n, d)

def diag_spec(n, f):
    return M(n, {x: {x: f(x)} for x in product((0, 1), repeat=n)})

G_Z  = {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): NEG}
G_X  = {(0, 0): ZERO, (0, 1): ONE, (1, 0): ONE, (1, 1): ZERO}
G_S  = {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): I_}
G_K  = {(0, 0): GINV, (0, 1): GINV, (1, 0): GINV, (1, 1): GINV * NEG}
G_iZ = {(0, 0): I_, (0, 1): ZERO, (1, 0): ZERO, (1, 1): MI}
def mul2(A, B):
    return {(r, c): sum((A[(r, k)] * B[(k, c)] for k in (0, 1)), ZERO) for r in (0, 1) for c in (0, 1)}
def inv2(A): return {(r, c): A[(c, r)].conj() for r in (0, 1) for c in (0, 1)}
G_XZ = mul2(G_X, G_Z)
G_ZX = mul2(G_Z, G_X)

# ----------------------------------------------------------------------
# The gadgets

def CCZ(a, b, c):
    return [('CS', a, c), ('CX', a, b), ('CS', b, c), ('CS', b, c), ('CS', b, c), ('CX', a, b), ('CS', b, c)]

def toff(t, c1, c2):
    return [('K', t)] + CCZ(t, c1, c2) + [('K', t), ('iI',)]

def CCZX(t, c1, c2): return CCZ(t, c1, c2) + toff(t, c1, c2)
def CCXZ(t, c1, c2): return toff(t, c1, c2) + CCZ(t, c1, c2)

TAU02 = {0: 2, 2: 0}
EX = {0: 1, 1: 0}

def box(k):
    if k == 0: return [('iI',), ('iI',)]
    if k == 1: return [('Z', 1)]
    if k == 2: return [('CS', 1, 2), ('CS', 1, 2)]
    B = relabel(up(box(k - 1)), TAU02)
    return CCZX(0, 1, 2) + B + CCXZ(0, 1, 2) + B

def rotXZ(k):
    B = relabel(box(k), EX)
    return [('CK', 1, 0)] + B + [('S', 1), ('CK', 1, 0)] + B

def rotZX(k): return inverse(rotXZ(k))

def cX(k):
    return [('K', 0)] + relabel(box(k + 1), EX) + [('K', 0), ('iI',)]

# TwoQubit's CK10 word, K on wire 0 controlled by wire 1.
CK10 = [('CS', 0, 1), ('K', 0), ('CS', 0, 1), ('K', 0), ('CS', 0, 1), ('S', 1), ('S', 1), ('S', 1), ('iI',)]

def check(name, ok):
    print(('ok   ' if ok else 'FAIL ') + name, flush=True)
    return ok

if __name__ == '__main__':
    allok = True
    allok &= check('CK10 word is Lambda_1(K_0)', matrix(2, CK10) == ctrl_spec(2, 0, [1], G_K))
    allok &= check('CCZ', matrix(3, CCZ(0, 1, 2)) == diag_spec(3, lambda x: NEG if all(x) else ONE))
    allok &= check('toff', matrix(3, toff(0, 1, 2)) == ctrl_spec(3, 0, [1, 2], G_X))
    allok &= check('CCZX = Lambda(ZX)', matrix(3, CCZX(0, 1, 2)) == ctrl_spec(3, 0, [1, 2], G_ZX))
    for k in range(0, 6):
        n = k + 1
        allok &= check(f'box {k}', matrix(n, box(k)) == diag_spec(n, lambda x: NEG if all(x[1:]) else ONE))
    for k in range(1, 6):
        n = k + 1
        allok &= check(f'rotXZ {k}', matrix(n, rotXZ(k)) == ctrl_spec(n, 0, list(range(1, k + 1)), G_XZ))
        allok &= check(f'rotZX {k}', matrix(n, rotZX(k)) == ctrl_spec(n, 0, list(range(1, k + 1)), G_ZX))
    for k in range(0, 5):
        n = k + 2
        allok &= check(f'cX {k}', matrix(n, cX(k)) == ctrl_spec(n, 0, list(range(2, k + 2)), G_X))

    # ------------------------------------------------------------------
    # The 1-qubit Clifford group, and the cheap elements
    gens = {'S': G_S, 'K': G_K, 'i': {(0, 0): I_, (0, 1): ZERO, (1, 0): ZERO, (1, 1): I_}}
    I2 = {(0, 0): ONE, (0, 1): ZERO, (1, 0): ZERO, (1, 1): ONE}
    key2 = lambda A: tuple(sorted((k, (v.r, v.i)) for k, v in A.items()))
    group = {key2(I2): (I2, '')}
    frontier = [(I2, '')]
    while frontier:
        nxt = []
        for A, w in frontier:
            for g, G in gens.items():
                B = mul2(A, G)
                kb = key2(B)
                if kb not in group:
                    group[kb] = (B, w + g); nxt.append((B, w + g))
        frontier = nxt
    print(f'1-qubit Clifford group: {len(group)} elements', flush=True)
    det2 = lambda A: A[(0, 0)] * A[(1, 1)] - A[(0, 1)] * A[(1, 0)]
    def conj_class(R):
        out = {}
        for kb, (U, w) in group.items():
            C = mul2(U, mul2(R, inv2(U)))
            out[key2(C)] = (C, w)
        return out
    refl = conj_class(G_Z)
    rots = conj_class(G_XZ)
    cheap = {}
    for kb, (C, w) in refl.items(): cheap[kb] = (C, 'Z', w)
    for kb, (C, w) in rots.items(): cheap[kb] = (C, 'XZ', w)
    print(f'reflections {len(refl)}, XZ-rotations {len(rots)}, cheap {len(cheap)}', flush=True)

    # Targets: iZ (the phase pair's core), and the hybrid's core K i^-1
    # on its own first index: K . diag(-i, 1) = (-i) K S (det 1).
    G2 = mul2(G_K, {(0, 0): MI, (0, 1): ZERO, (1, 0): ZERO, (1, 1): ONE})
    targets = {'iZ': G_iZ, 'K i_a^-1': G2}
    cheap_list = list(cheap.values())
    for name, T in targets.items():
        found = []
        for A, ka, wa in cheap_list:
            Ai = inv2(A)
            for B, kb, wb in cheap_list:
                C = mul2(A, mul2(B, mul2(Ai, inv2(B))))
                if C == T:
                    found.append((ka, wa, kb, wb))
        print(f'{name} = [A, B] with A, B cheap: {len(found)} pairs; e.g. {found[:4]}', flush=True)
    print('ALL OK' if allok else 'SOME FAILED')
