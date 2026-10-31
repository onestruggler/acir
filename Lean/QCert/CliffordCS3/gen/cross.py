"""Commutations of three-qubit gates that lie in no common tabled group.

`commute(P, a, b, how)` proves a b = b a: directly (`prove_any`), letter by letter, or by
splitting one side into factors (`how = ('A' | 'B', factors, sub-hows)`), each factor proved
to commute with the other side.

`cross_comm(P, X, Y, s)`: X and Y are Pauli-type gates (permutations or diagonals with phases
+-1) on different targets, supported on opposite values of the qubit s; X = C D C^-1 with C the
K on X's target controlled by s (a gate on two qubits) and D diagonal, Y = K D' K^-1 with K the
K on Y's target (the third qubit) and D' diagonal; then Y commutes with C letter by letter (K)
and in Y's... see `cross_comm`.
"""
import numpy as np
from collections import deque
from table import Deriv, invert
from qc import key, eq
from pc import prove_any

DIAG = ['i', 'S0', 'S1', 'S2', 'C01', 'C12', 'C02', 'CCZ']


def inv_word(P, u):
    return P.W.inv.word(tuple(u))


def short_word(P, letters, m, maxlen=12):
    mats = P.A.mats
    target = key(m)
    e = np.eye(8, dtype=complex)
    if key(e) == target:
        return ()
    seen = {key(e)}
    dq = deque([((), e)])
    while dq:
        wd, mm = dq.popleft()
        if len(wd) >= maxlen:
            continue
        for a in letters:
            p = mm @ mats[a]
            k = key(p)
            if k == target:
                return wd + (a,)
            if k not in seen:
                seen.add(k)
                dq.append((wd + (a,), p))
    return None


def matw(P, u):
    return P.A.matw(tuple(u))


def letterwise(P, a, b):
    """a b = b a for words whose letters commute pairwise."""
    T = P.T
    a, b = tuple(a), tuple(b)
    D = Deriv(T, a + b)
    m = len(a)
    for j in range(len(b)):
        for i in range(m - 1, -1, -1):
            pos = j + i
            x, y = D.w[pos], D.w[pos + 1]
            e = prove_any(P, (x, y), (y, x))
            if e is not None:
                D.step(pos, e, True)
    assert D.w == b + a
    return T.derived(a + b, b + a, D.steps)


def commute(P, a, b, how=None):
    """a b = b a.  how: None (directly, else letter by letter), 'L' (letter by letter), or
    ('A', factors, hows) / ('B', factors, hows): a (resp. b) is the product of the factors
    (proved by prove_any), each commuting with b (resp. a) by the corresponding how."""
    T = P.T
    a, b = tuple(a), tuple(b)
    if how is None:
        try:
            e = prove_any(P, a + b, b + a)
            return e
        except (ValueError, AssertionError):
            return letterwise(P, a, b)
    if how == 'L':
        return letterwise(P, a, b)
    side, factors, hows = how
    factors = [tuple(f) for f in factors]
    cat = tuple(x for f in factors for x in f)
    if side == 'A':
        ea = prove_any(P, a, cat)
        D = Deriv(T, a + b)
        if ea is not None:
            D.step(0, ea, True)
        # move b left past the factors, last first
        pos = len(cat)
        for f, h in reversed(list(zip(factors, hows))):
            pos -= len(f)
            e = commute(P, f, b, h)
            if e is not None:
                D.step(pos, e, True)
        if ea is not None:
            D.step(len(b), ea, False)
        assert D.w == b + a
        return T.derived(a + b, b + a, D.steps)
    else:
        eb = prove_any(P, b, cat)
        D = Deriv(T, a + b)
        if eb is not None:
            D.step(len(a), eb, True)
        pos = 0
        for f, h in zip(factors, hows):
            e = commute(P, a, f, h)
            if e is not None:
                D.step(pos, e, True)
            pos += len(f)
        if eb is not None:
            D.step(0, eb, False)
        assert D.w == b + a
        return T.derived(a + b, b + a, D.steps)


# ---------------------------------------------------------------------- controlled K's
CSL = {(0, 1): 'C01', (1, 2): 'C12', (0, 2): 'C02'}


def ctrl_mat(U1, target, c, val):
    m = np.zeros((8, 8), dtype=complex)
    for x in range(8):
        bits = [(x >> 2) & 1, (x >> 1) & 1, x & 1]
        if bits[c] != val:
            m[x, x] = 1
            continue
        for a in range(2):
            b = bits[target]
            yb = list(bits)
            yb[target] = a
            y = yb[0] * 4 + yb[1] * 2 + yb[2]
            m[y, x] += U1[a, b]
    return m


KM = np.array([[1, 1], [1, -1]]) / (1 + 1j)


class Ctrl:
    """Words for the K on qubit t controlled by qubit s (value x), over K_t, S_t, S_s, CS_st, i."""

    def __init__(self, P):
        self.P = P
        self.words = {}

    def word(self, t, s, x):
        k = (t, s, x)
        if k not in self.words:
            P = self.P
            cs = CSL[tuple(sorted((s, t)))]
            L = ['K%d' % t, 'S%d' % t, 'S%d' % s, cs, 'i']
            m = ctrl_mat(KM, t, s, x)
            wd = short_word(P, L, m, maxlen=14)
            assert wd is not None, k
            self.words[k] = wd
        return self.words[k]


def support_vals(m):
    """The qubit values fixed on the support (states moved or rephased) of m."""
    sup = [x for x in range(8) if not (abs(m[x, x] - 1) < 1e-9 and
                                        all(abs(m[y, x]) < 1e-9 for y in range(8) if y != x))]
    vals = {}
    for q in range(3):
        vs = {(x >> (2 - q)) & 1 for x in sup}
        if len(vs) == 1:
            vals[q] = vs.pop()
    return vals


def target_of(m):
    """The qubit a Pauli-type transposition flips."""
    for x in range(8):
        for y in range(8):
            if x != y and abs(m[y, x]) > 1e-9:
                d = x ^ y
                return {4: 0, 2: 1, 1: 2}.get(d)
    return None


def cross_how(P, CT, X, Y, s=None):
    """The `how` for X Y = Y X, X and Y Pauli-type gates (one transposition with phases) on
    different targets, supported on opposite values of the third qubit s: X = C D C^-1 with C
    the K on X's target controlled by s, D diagonal; Y = K D' K^-1 with K the K on Y's target,
    D' diagonal.  C commutes with K letter by letter and with D' in X's block group; D commutes
    with Y in Y's block group."""
    mX, mY = matw(P, X), matw(P, Y)
    tX, tY = target_of(mX), target_of(mY)
    vX, vY = support_vals(mX), support_vals(mY)
    if s is None:
        s = next(q for q in range(3) if q in vX and q in vY and vX[q] != vY[q])
    assert tX is not None and tY is not None and len({tX, tY, s}) == 3, (tX, tY, s)
    C = CT.word(tX, s, vX[s])
    Ci = inv_word(P, C)
    D = short_word(P, DIAG, np.linalg.inv(matw(P, C)) @ mX @ matw(P, C), maxlen=8)
    assert D is not None, ('D', X)
    KY = ('K%d' % tY,)
    KYi = inv_word(P, KY)
    Dp = short_word(P, DIAG, np.linalg.inv(matw(P, KY)) @ mY @ matw(P, KY), maxlen=8)
    assert Dp is not None, ('Dp', Y)
    hC = ('B', [KY, Dp, KYi], ['L', None, 'L'])
    return ('A', [C, D, Ci], [hC, None, hC])


def cross_comm(P, CT, X, Y, s=None):
    return commute(P, X, Y, cross_how(P, CT, X, Y, s))


def block_cross_comm(P, CT, X, Y):
    """Commute an arbitrary single-target block with an opposite-face Pauli.

    Search for X over controlled K and diagonals commuting with Y.  The
    equality to that word is proved in the finite block group; commuting its
    factors uses the same block group and disjoint-wire commutations.
    """
    from ctv import word_of
    mX, mY = matw(P, X), matw(P, Y)
    tX, tY = target_of(mX), target_of(mY)
    vX, vY = support_vals(mX), support_vals(mY)
    s = next(q for q in range(3) if q in vX and q in vY and vX[q] != vY[q])
    assert len({tX, tY, s}) == 3
    C = CT.word(tX, s, vX[s])
    name = 'CK%d%d%d' % (tX, s, vX[s])
    if name not in P.A.mats:
        P.A.define(name, C)
    diagonal = [a for a in DIAG if eq(P.A.mats[a] @ mY, mY @ P.A.mats[a])]
    for a in DIAG:
        for b in DIAG:
            if a == b:
                continue
            dw = (a, b, b, b)
            dm = matw(P, dw)
            if not eq(dm @ mY, mY @ dm):
                continue
            if a in diagonal and b in diagonal:
                continue
            dn = 'DC_' + a + '_' + b
            if dn not in P.A.mats:
                P.A.define(dn, dw)
            diagonal.append(dn)
    wd = short_word(P, [name] + [a for a in diagonal if a.startswith(('C', 'DC'))], mX, maxlen=16)
    assert wd is not None, ('block word', X, Y, diagonal)
    KY = ('K%d' % tY,)
    KYi = inv_word(P, KY)
    Dp = short_word(P, DIAG, np.linalg.inv(matw(P, KY)) @ mY @ matw(P, KY), maxlen=8)
    assert Dp is not None
    hC = ('A', [C], [('B', [KY, Dp, KYi], ['L', None, 'L'])])
    return commute(P, X, Y, ('A', [(z,) for z in wd], [hC if z == name else None for z in wd]))
