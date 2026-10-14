# The decoding of P' into n-qubit circuits, as the Agda definition will
# spell it, checked exactly against the letters' matrices at the Gray
# numbering (code k = k xor (k >> 1), wire i = bit i, as
# Real-Clifford+CH.Auxiliary.Gray through Clifford+CS.Numbering).
#
# Words are in operator order throughout (w . v denotes [w][v], v acts
# first), as circuits, two-level words and P'-words all are.  A wire
# permutation stands for conjugation by a swap network.
#
# Frames (width m + 3):
#   Sbox m   [U=0, T=1, c=2..m+1, A=m+2]   L^m(S) on T from the controls c,
#            borrowed wire A, box wire U:
#            Sbox m = box(m+2) . [Toff(A; m, m+1), tau(m,m+2)(Sbox(m-1) v)]
#   Kbox m   [U=0, A=1, c=2..m+1, T=m+2]   L^m(K) on T:
#            Kbox m = Sbox(m)^3 . [Toff(A; 2, 3), tau(1,3)(Kbox(m-1) ^)]
# Base gadgets at width n (target 0, controls 1..n-1 black):
#   G_pp  = [Toff(0;1,2), L_{3..}(S_0)]               = L^{n-1}(iZ)   (i at bit 0)
#   G_rot = [CK(1->0), Z on {0,2..} box wire 1]      = L^{n-1}(XZ)
#   G_ki  = [Barenco(V=S^2KS on 0;1,2), L_{3..}(K_0)] = L^{n-1}(XKX diag(1,-i))
# placed by a layout (target to wire 0, white controls by X) and
# oriented by the bit of the first index at the target (X on the target).
import sys
from itertools import product, combinations
from random import Random
from gadgets import (Q, M, ZERO, ONE, I_, MI, NEG, GINV, matrix, relabel, up,
                     inverse, box, toff, CCZ, check, mul2, inv2, G_K, G_S, G_X)

# ----------------------------------------------------------------------
# Gray numbering

def code(n, k):
    g = k ^ (k >> 1)
    return tuple((g >> i) & 1 for i in range(n))

def diff_wire(x, y):
    d = [i for i in range(len(x)) if x[i] != y[i]]
    assert len(d) == 1, (x, y)
    return d[0]

# ----------------------------------------------------------------------
# Boxes

def Sbox(m):
    if m == 0: return [('S', 1)]
    if m == 1: return [('CS', 1, 2)]
    Zb = box(m + 2)
    Tf = toff(m + 2, m, m + 1)
    Ch = relabel(Sbox(m - 1), {m: m + 2, m + 2: m})
    return Zb + Tf + Ch + Tf + inverse(Ch)

def Kbox(m):
    if m == 0: return [('K', 2)]
    if m == 1: return [('CK', 2, 3)]
    Sb = Sbox(m)
    Tf = toff(1, 2, 3)
    Ch = relabel(up(Kbox(m - 1)), {1: 3, 3: 1})
    return Sb + Sb + Sb + Tf + Ch + Tf + inverse(Ch)

# the controlled functor on one qubit and Barenco's CC(V^2)
def ctrlw(word1, c, t):
    out = []
    for g in word1:
        out.append({'S': ('CS', c, t), 'K': ('CK', c, t), 'i': ('S', c)}[g])
    return out

def inv1(word1):
    out = []
    for g in reversed(word1):
        out += {'S': ['S', 'S', 'S'], 'K': ['K', 'i'], 'i': ['i', 'i', 'i']}[g]
    return out

def barenco(wv, c1, c2, t):
    return (ctrlw(wv, c1, t) + [('CX', c1, c2)] + ctrlw(inv1(wv), c2, t)
            + [('CX', c1, c2)] + ctrlw(wv, c2, t))

# ----------------------------------------------------------------------
# Base gadgets at width n

def G_pp(n):
    m = n - 3
    Tf = toff(0, 1, 2)
    pi = {0: 1, 1: 0, m + 2: 2}
    pi.update({j: j + 1 for j in range(2, m + 2)})
    SB = relabel(Sbox(m), pi)
    return Tf + SB + Tf + SB + SB + SB

def G_rot(n):          # XZ
    B = relabel(box(n - 1), {0: 1, 1: 0})
    return [('CK', 1, 0)] + B + [('S', 1), ('CK', 1, 0)] + B

def G_ki(n):
    m = n - 3
    Bar = barenco('SSKS', 1, 2, 0)
    pi = {0: 1, 1: 2, m + 2: 0}
    pi.update({j: j + 1 for j in range(2, m + 2)})
    KB = relabel(Kbox(m), pi)
    return Bar + KB + inverse(Bar) + inverse(KB)

# ----------------------------------------------------------------------
# Placement by a layout: the target wire to 0 (the wires below it up
# one), X on the white controls, X on the target for the orientation

def place(n, t, colours, beta, gate):
    # base wire 0 (the target) to t, base wires 1..t down to 0..t-1
    pi = {0: t}
    pi.update({w + 1: w for w in range(t)})
    g = relabel(gate, pi)
    if beta: g = [('X', t)] + g + [('X', t)]
    negs = [('X', w) for w in range(n) if w != t and colours[w] == 0]
    return negs + g + negs

def layout(n, a):
    """target wire and colours for the consecutive pair a, a+1."""
    x, y = code(n, a), code(n, a + 1)
    return diff_wire(x, y), x

# ----------------------------------------------------------------------
# The decoding

class Dec:
    def __init__(self, n):
        self.n = n; self.N = 2 ** n
        self.gpp, self.grot, self.gki = G_pp(n), G_rot(n), G_ki(n)
        self.memo = {}; self.mmemo = {}

    def gm(self, key):
        """the matrix of a placed gadget, memoized."""
        if key not in self.mmemo: self.mmemo[key] = matrix(self.n, self.gadget(*key))
        return self.mmemo[key]

    def mat(self, keys):
        R = M.ident(self.n)
        for key in keys: R = R * self.gm(key)
        return R

    def gadget(self, kind, a, flip=False):
        """the gadget for the pair a, a+1; flip exchanges the roles of a
        and a+1 (the inverse phase pair, the other rotation)."""
        key = (kind, a, flip)
        if key in self.memo: return self.memo[key]
        t, x = layout(self.n, a)
        beta = x[t] ^ (1 if flip else 0)
        base = {'pp': self.gpp, 'rot': self.grot, 'ki': self.gki}[kind]
        if kind == 'ki': beta ^= 1          # G_ki has a at bit 1
        w = place(self.n, t, x, beta, base)
        self.memo[key] = w
        return w

    # i_a i_b^-1
    def pp(self, a, b):
        if a < b: return [('pp', k, False) for k in range(a, b)]
        if a > b: return [('pp', k, True) for k in range(b, a)]
        return []

    # (-1)_a X_{a,a+1} and (-1)_{a+1} X_{a,a+1}
    def lo1(self, a): return [('rot', a, False)]
    def hi1(self, a): return [('rot', a, True)]

    # (-1)_a X_{a,a+d} and (-1)_{a+d} X_{a,a+d}, by the shrink rules
    # px-shrink_1 and px-shrink_2 from the bottom (no parity condition)
    def lo(self, a, d):
        if d == 0: return []
        if d == 1: return self.lo1(a)
        return self.hi1(a) + self.lo(a + 1, d - 1) + self.lo1(a)
    def hi(self, a, d):
        if d == 0: return []
        if d == 1: return self.hi1(a)
        return self.hi1(a) + self.hi(a + 1, d - 1) + self.lo1(a)

    # (-1)_c X_{a,b}, a < b
    def px(self, c, a, b):
        if c == a: return self.lo(a, b - a)
        if c == b: return self.hi(a, b - a)
        return self.pp(c, a) + self.pp(c, a) + self.px(a, a, b)

    # X_{a,b} X_{c,d}
    def dx(self, a, b, c, d): return self.px(a, a, b) + self.px(b, c, d)

    # K_{a,b} i_a^-1, a < b: the gap closed by consecutive rotations
    def kia(self, a, b):
        if b == a + 1: return [('ki', a, False)]
        return self.hi1(a) + self.kia(a + 1, b) + self.lo1(a)

    # K_{a,b} i_s^-1
    def ki(self, a, b, s): return self.kia(a, b) + self.pp(a, s)

# ----------------------------------------------------------------------
# The letters' matrices

def letter_matrix(n, kind, *idx):
    N = 2 ** n
    cd = lambda k: code(n, k)
    d = {x: {x: ONE} for x in product((0, 1), repeat=n)}
    if kind == 'pp':
        a, b = idx
        d[cd(a)] = {cd(a): d[cd(a)][cd(a)] * I_}
        d[cd(b)] = {cd(b): d[cd(b)][cd(b)] * MI}
        return M(n, d)
    if kind == 'px':      # (-1)_c X_ab : exchange, then the sign
        c, a, b = idx
        P = M(n, dict(d)); P.d[cd(a)] = {cd(b): ONE}; P.d[cd(b)] = {cd(a): ONE}
        D = M(n, {x: {x: ONE} for x in product((0, 1), repeat=n)}); D.d[cd(c)] = {cd(c): NEG}
        return D * P
    if kind == 'dx':
        a, b, c, dd = idx
        P = M(n, dict(d)); P.d[cd(a)] = {cd(b): ONE}; P.d[cd(b)] = {cd(a): ONE}
        Q2 = M(n, {x: {x: ONE} for x in product((0, 1), repeat=n)}); Q2.d[cd(c)] = {cd(dd): ONE}; Q2.d[cd(dd)] = {cd(c): ONE}
        return P * Q2
    if kind == 'ki':      # K_ab . i_s^-1
        a, b, s = idx
        Km = M(n, dict(d))
        Km.d[cd(a)] = {cd(a): GINV, cd(b): GINV}
        Km.d[cd(b)] = {cd(a): GINV, cd(b): GINV * NEG}
        D = M(n, {x: {x: ONE} for x in product((0, 1), repeat=n)}); D.d[cd(s)] = {cd(s): MI}
        return Km * D
    raise ValueError(kind)

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    full = n <= 4
    D = Dec(n); N = D.N
    rng = Random(1)
    allok = True
    # the three base gadgets, raw and in each orientation
    t0, x0 = layout(n, 0)
    for kind, a in (('pp', 0), ('rot', 0), ('ki', 0), ('pp', 5), ('rot', 5), ('ki', 5)):
        w = D.gadget(kind, a)
        if kind == 'pp': exp = letter_matrix(n, 'pp', a, a + 1)
        elif kind == 'rot': exp = letter_matrix(n, 'px', a, a, a + 1)
        else: exp = letter_matrix(n, 'ki', a, a + 1, a)
        allok &= check(f'gadget {kind} at {a} ({len(w)} gates)', matrix(n, w) == exp)
    pairs = list(combinations(range(N), 2))
    # pp
    cases = [(a, b) for a in range(N) for b in range(N)] if full else [(rng.randrange(N), rng.randrange(N)) for _ in range(40)]
    bad = [(a, b) for a, b in cases if D.mat(D.pp(a, b)) != letter_matrix(n, 'pp', a, b)]
    allok &= check(f'pp: {len(cases)} cases, {len(bad)} bad {bad[:4]}', not bad)
    # px
    cases = [(c, a, b) for (a, b) in pairs for c in range(N)] if full else [(rng.randrange(N),) + rng.choice(pairs) for _ in range(60)]
    bad = [cs for cs in cases if D.mat(D.px(*cs)) != letter_matrix(n, 'px', *cs)]
    allok &= check(f'px: {len(cases)} cases, {len(bad)} bad {bad[:4]}', not bad)
    # dx (a sample)
    cases = [rng.choice(pairs) + rng.choice(pairs) for _ in range(120 if full else 30)]
    bad = [cs for cs in cases if D.mat(D.dx(*cs)) != letter_matrix(n, 'dx', *cs)]
    allok &= check(f'dx: {len(cases)} cases, {len(bad)} bad {bad[:4]}', not bad)
    # ki
    cases = [(a, b, s) for (a, b) in pairs for s in range(N)] if full else [rng.choice(pairs) + (rng.randrange(N),) for _ in range(60)]
    bad = [cs for cs in cases if D.mat(D.ki(*cs)) != letter_matrix(n, 'ki', *cs)]
    allok &= check(f'ki: {len(cases)} cases, {len(bad)} bad {bad[:4]}', not bad)
    print('ALL OK' if allok else 'SOME FAILED')
