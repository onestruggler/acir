# Transport of two-wire equations under the control, and de-borrowing.
#
# TR2 axioms.  For two circuits u, v on the domain wires 2, 3 with the
# same operator, lambda1_4(u) = lambda1_4(v) is an axiom `TR2-<n>` of the
# five-wire derivations.  In Agda it is Five.Transport's transport of a
# two-wire derivation (complete on two wires, then rule by rule through
# the (F1) items at the offsets 2, 3, 4, which no four- or three-wire
# rule occupies), so it rests on nothing that this file derives.  It is
# used at any renaming of the five wires.
#
# De-borrowing (the joint paper's Lemma de-borrowing).  Let w be a circuit
# on the wires y = 2, x = 3, block diagonal in y: on y = 0 it acts as P,
# on y = 1 as P W, with det W = +-1.  Write Z^e W = g^-1 U^-1 g U with
# one-wire circuits g, U (U in S, S^3, K), and
#   Lambda = lambda1(P_x) CCZ(t, y, x)^e C_y(g^-1) lambda1(U^-1) C_y(g) lambda1(U),
# a circuit on the three wires t = 4, y, x (C_y the letterwise y-controlled
# version).  Then lambda1(w) = Lambda: by TR2 lambda1(w) is lambda1 of
# P CZ^e a U^-1 b U (a = C_y(g^-1), b = C_y(g)); lambda1(CZ) is an S-box
# squared, the CCZ; and a, b split into lambda0 lambda1 (F5, F4), whose
# lambda0 halves meet and cancel (TR2 again, between X4's).
import hashlib
import cs, derivn, f1, f1rules, lamcalc
from derivn import Derivation, show, norm1
from lamcalc import ID, L0, L1, G

P_ = cs.P
I_ = cs.I
GINV = cs.GINV

TRS = []                       # (name, u, v): the TR2 axioms, canonical frame


# ------------------------------------------------------------ generator words
# Generators as in lamcalc: ('I',), ('S', v), ('K', v), ('CS', v) (on v, v + 1).

def rel_gens(gs, pi):
    out = []
    for g in gs:
        if g[0] == 'I':
            out.append(g)
        elif g[0] in ('S', 'K'):
            out.append((g[0], pi.get(g[1], g[1])))
        else:
            a, b = pi.get(g[1], g[1]), pi.get(g[1] + 1, g[1] + 1)
            assert abs(a - b) == 1, ('CS not adjacent after renaming', g, pi)
            out.append(('CS', min(a, b)))
    return out


def letters(gs):
    return [x for g in gs for x in G(g, ID)]


def l1(gs, pi=ID): return [x for g in gs for x in L1(g, pi)]
def l0(gs, pi=ID): return [x for g in gs for x in L0(g, pi)]


def gens_of(ls):
    out = []
    for g in ls:
        if g[0] == 'iI':
            out.append(('I',))
        elif g[0] in ('S', 'K'):
            out.append(g)
        else:
            out.append(('CS', min(g[1:])))
    return out


def inv1(gs):
    """the inverse word of a one-wire word: S^-1 = S S S, K^-1 = K i, i^-1 = i i i."""
    out = []
    for g in reversed(gs):
        if g[0] == 'S':
            out += [g, g, g]
        elif g[0] == 'K':
            out += [g, ('I',)]
        else:
            out += [('I',)] * 3
    return out


def ctrl(gs, y, x):
    """the letterwise y-controlled version of a one-wire word on x."""
    o = min(x, y)
    out = []
    for g in gs:
        if g[0] == 'S':
            out.append(('CS', o))
        elif g[0] == 'K':
            out += [('CS', o), ('K', x), ('CS', o), ('K', x), ('CS', o)] + [('S', y)] * 3 + [('I',)]
        else:
            out.append(('S', y))
    return out


# ------------------------------------------------------------ one-wire matrices
def mmul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) % P_ for j in range(2)) for i in range(2))


ONE = ((1, 0), (0, 1))
MAT = {'S': ((1, 0), (0, I_)), 'K': ((GINV, GINV), (GINV, (P_ - GINV) % P_)), 'I': ((I_, 0), (0, I_))}


def mat1(gs):
    M = ONE
    for g in gs:
        M = mmul(M, MAT[g[0]])
    return M


def group1(x):
    """every one-wire operator on x, with a shortest word over S, K, i."""
    gens = [('S', x), ('K', x), ('I',)]
    words = {ONE: []}
    frontier = [ONE]
    while frontier:
        nxt = []
        for M in frontier:
            for g in gens:
                N = mmul(M, MAT[g[0]])
                if N not in words:
                    words[N] = words[M] + [g]
                    nxt.append(N)
        frontier = nxt
    return words


GROUP = {}


def word_of(M, x):
    if x not in GROUP:
        GROUP[x] = group1(x)
    return GROUP[x][M]


def det(M): return (M[0][0] * M[1][1] - M[0][1] * M[1][0]) % P_


def minv(M):
    d = pow(det(M), P_ - 2, P_)
    return ((M[1][1] * d % P_, (P_ - M[0][1]) * d % P_), ((P_ - M[1][0]) * d % P_, M[0][0] * d % P_))


Z = ((1, 0), (0, P_ - 1))


# ------------------------------------------------------------ the two-wire semantics
def mat2(gs, y, x):
    """the operator of a word on the wires y, x as its two blocks in y
    (None if it is not block diagonal), by acting on basis vectors."""
    sem = cs.Sem(5)
    blocks = {}
    for yb in (0, 1):
        cols = []
        for xb in (0, 1):
            v = [0] * 32
            v[(yb << y) | (xb << x)] = 1
            for g in reversed(letters(gs)):
                v = sem.apply(norm1(g) if g[0] != 'iI' else g, v)
            cols.append(v)
        for xb in (0, 1):
            for yb2 in (0, 1):
                for xb2 in (0, 1):
                    val = cols[xb][(yb2 << y) | (xb2 << x)]
                    if yb2 != yb and val:
                        return None
        blocks[yb] = tuple(tuple(cols[j][(yb << y) | (i << x)] for j in (0, 1)) for i in (0, 1))
    return blocks


def twisted(W, x):
    """e, g, U with Z^e W = g^-1 U^-1 g U, U in S, S^3, K."""
    Us = [[('S', x)], [('S', x)] * 3, [('K', x)]]
    best = None
    for e in (0, 1):
        T = mmul(Z, W) if e else W
        for U in Us:
            MU = mat1(U)
            for Mg, g in word_of_all(x):
                if mmul(mmul(minv(Mg), minv(MU)), mmul(Mg, MU)) == T:
                    cand = (len(g) + len(U) + e, e, g, U)
                    if best is None or cand[0] < best[0]:
                        best = cand
                    break
    assert best, 'no twisted form'
    return best[1:]


def word_of_all(x):
    if x not in GROUP:
        GROUP[x] = group1(x)
    return sorted(GROUP[x].items(), key=lambda kv: len(kv[1]))


# ------------------------------------------------------------ TR2
def tr2_axiom(L, u, v):
    """the axiom lambda1(u) = lambda1(v) for u, v on the wires 2, 3."""
    for g in u + v:
        assert g[0] == 'I' or (g[0] in ('S', 'K') and g[1] in (2, 3)) or (g[0] == 'CS' and g[1] == 2), g
    assert derivn.fp(letters(u)) == derivn.fp(letters(v)), 'TR2: not the same operator'
    for nm, u2, v2 in TRS:
        if (u2, v2) == (u, v):
            return nm
    # named by its content, so that separate runs agree on the names
    nm = 'TR2-' + hashlib.md5(repr((u, v)).encode()).hexdigest()[:8]
    L[nm] = (derivn.norm(l1(u)), derivn.norm(l1(v)))
    TRS.append((nm, list(u), list(v)))
    return nm


def tr2(d, k, cu, cv, pi=ID):
    """the transport for the canonical words cu, cv, at the renaming pi, at
    k: a `transport` step of the frame's letters (control wire pi(4))."""
    nm = tr2_axiom(d.lemmas, cu, cv)
    src = derivn.relabel_word(l1(cu), pi); dst = derivn.relabel_word(l1(cv), pi)
    el = derivn.relabel_word(letters(cu), pi); er = derivn.relabel_word(letters(cv), pi)
    d.transport(k, src, dst, el, er, pi.get(4, 4), 1)
    return nm


# ------------------------------------------------------------ de-borrowing
def deborrow(L, name, w, y=2, x=3):
    """the lemma lambda1(w) = Lambda (canonical frame); returns (name, Lambda)."""
    if name in L:
        return name, L[name][1]
    B = mat2(w, y, x)
    assert B is not None, f'{name}: not block diagonal'
    P0, P1 = B[0], B[1]
    W = mmul(minv(P0), P1)
    assert det(W) in (1, P_ - 1), f'{name}: det W = {det(W)}'
    e, g, U = twisted(W, x)
    Pw = word_of(P0, x)
    ginv = inv1(g)
    Uinv = inv1(U)
    a, b = ctrl(ginv, y, x), ctrl(g, y, x)
    cz = [('CS', min(x, y))] * 2 * e
    w2 = Pw + cz + a + Uinv + b + U
    assert derivn.fp(letters(w2)) == derivn.fp(letters(w)), f'{name}: twisted form wrong'
    ccz = [norm1(('CCZ', 4, y, x))] * e
    Lam = l1(Pw) + ccz + letters(a) + l1(Uinv) + letters(b) + l1(U)
    # the lambda0 halves of a, b cancel
    eps = f'{name}-eps'
    d = Derivation(eps, l0(a) + l0(b), [], L)
    k = 0
    while k + 1 < len(d.cur):
        if d.cur[k] == ('X', 4) and d.cur[k + 1] == ('X', 4):
            d.win(k, 2, [])
        else:
            k += 1
    assert d.cur[0] == ('X', 4) and d.cur[-1] == ('X', 4), show(d.cur)
    tr2(d, 1, a + b, [])
    d.win(0, 2, [])
    d.done()
    # a and b split
    for nm_, ws in ((f'{name}-split-a', a), (f'{name}-split-b', b)):
        d = Derivation(nm_, letters(ws), l0(ws) + l1(ws), L)
        lamcalc.split(d, 0, ws, ID)
        d.done()
    d = Derivation(name, l1(w), Lam, L)
    tr2(d, 0, w, w2)
    p = len(l1(Pw))
    if e:
        S = d.cur[p]
        d.lemma(f1.s2(L, S), p)
        p += 1
    d.lemma(eps, p, fwd=False)                       # L0(a) L0(b) inserted
    na, nb = len(l0(a)), len(l0(b))
    lamcalc.bubble(d, p + na, b, a + Uinv, ID)       # L0(a) L1(a) L1(Uinv) L0(b) L1(b) L1(U)
    d.lemma(f'{name}-split-a', p, fwd=False)
    q = p + len(letters(a)) + len(l1(Uinv))
    d.lemma(f'{name}-split-b', q, fwd=False)
    d.done()
    return name, Lam


if __name__ == '__main__':
    # the twisted forms of the pieces de-borrowing meets
    X0 = gens_of(f1rules.X(2))
    CK = gens_of(f1rules.CK(2))
    A = X0 + CK + X0
    D = X0 + [('CS', 2)] + X0
    for nm, w in (('AD', A + D), ('CK.CS', CK + [('CS', 2)]),
                  ('CS K CS', [('CS', 2), ('K', 3), ('CS', 2)])):
        B = mat2(w, 2, 3)
        W = mmul(minv(B[0]), B[1])
        e, g, U = twisted(W, 3)
        print(nm, 'det W', det(W) == 1 and 1 or -1, 'e', e, 'g', g, 'U', U, 'P', word_of(B[0], 3))
