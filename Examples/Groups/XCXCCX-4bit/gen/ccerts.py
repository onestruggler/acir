"""Certificates for the controlled A8 over the labels of CLabels.

A model of CRel's decided side conditions (conj-ok, klein-ok) and of
LabelEngine's moves, exactly as the Agda computes them, and:

* PhiQ: each symbol γ c d of EvenRS 8 as a word of labels whose
  controlled matchings act on the upper half as f (γ c d);
* the 54 relations of EvenRS 8 under PhiQ, certified by LabelEngine
  moves (found by c8/certgen.py at the level of double transpositions
  and expanded; remapped to CLabels' numbering here and replayed);
* rev certificates: PhiQ x reversed is PhiQ of the inverse symbol;
* the closure: every label is reached from mu0 by conjugating with
  PhiQ of a symbol (a BFS tree: parent, symbol, depth), mu0 being PhiQ
  of γ₂ γ₄ γ₆ by a certificate of eight moves.

Conventions are Agda's: positions 0..7 are Width3's Gray states; act w
is the inverse action, act (u . v) = act u o act v; the matching of the
frame of G by a Coxeter word F is act F o mu0 o act F^-1.
"""
import os
import sys
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, 'c8'))
from clabels import PMS, IDX, plist, ORBIT, word_of, inverse, from_pairs, MU0  # noqa: E402
from mk_clabels import base_words  # noqa: E402

N8 = range(8)
BASEW = base_words()


def inv(w):
    return list(reversed(w))


def actf(w, x):
    for d in reversed(w):
        x = d + 1 if x == d else (d if x == d + 1 else x)
    return x


def matchf(w):
    a = [actf(w, x) for x in N8]
    ai = inverse(tuple(a))
    return tuple(a[MU0[ai[x]]] for x in N8)


def eq_match(p, q):
    return matchf(p) == matchf(q)


FRM = [word_of(tuple(plist(m))) for m in PMS]
for _i, _m in enumerate(PMS):
    assert matchf(FRM[_i]) == _m
TBL = PMS
MU0_IDX = IDX[MU0]


def find(table):
    return IDX.get(tuple(table))


def c3(x, y):
    tx, ty = TBL[x], TBL[y]
    z = find(tx[ty[tx[p]]] for p in N8)
    return x if z is None else z


def mul(x, y):
    tx, ty = TBL[x], TBL[y]
    z = find(tx[ty[p]] for p in N8)
    return x if z is None else z


def in_c(r):
    return all(actf(r, MU0[x]) == MU0[actf(r, x)] for x in N8)


def bc0_ok(F):
    m = find(matchf(F))
    if m is None:
        return False
    k, c = ORBIT[m]
    return eq_match(F, c + BASEW[k]) and in_c(c) and in_c(inv(c))


W0 = [0, 2, 4, 6]


def cP(F):
    return F + W0 + inv(F)


def bc_ok(x, y):
    fx, fy = FRM[x], FRM[y]
    return eq_match(fx + inv(fx) + fy, fy) and bc0_ok(inv(fx) + fy)


def conj_ok(x, y):
    return eq_match(cP(FRM[x]) + FRM[y], FRM[c3(x, y)]) and bc_ok(x, y)


KAPPA = [1, 2, 1, 4, 5, 4]


def klein_list(x, y):
    tx, ty = TBL[x], TBL[y]
    a = 0
    orb = [a, tx[a], ty[a], tx[ty[a]]]
    b = a
    for p in range(1, 8):
        if p not in orb:
            b = p
            break
    return orb + [b, tx[b], ty[b], tx[ty[b]]]


def match_with_frame(ts, w):
    """matchF of (frame ts . w): act = ts o act w."""
    a = [ts[actf(w, x)] for x in N8]
    ai = inverse(tuple(a))
    return tuple(a[MU0[ai[x]]] for x in N8)


def klein_ok(x, y):
    ts = klein_list(x, y)
    if len(set(ts)) != 8:
        return False
    return (matchf(FRM[x]) == match_with_frame(ts, [])
            and matchf(FRM[y]) == match_with_frame(ts, BASEW[1])
            and matchf(FRM[mul(x, y)]) == match_with_frame(ts, KAPPA))


# ---------------------------------------------------------------- the engine

def local(mv, w):
    k = mv[0]
    if k == 'H':
        if len(w) < 2 or not conj_ok(w[0], w[1]):
            return None
        return [c3(w[0], w[1]), w[0]] + w[2:]
    if k == 'Hi':
        if len(w) < 2 or not conj_ok(w[1], w[0]):
            return None
        return [w[1], c3(w[1], w[0])] + w[2:]
    if k == 'C':
        if len(w) < 2 or w[0] != w[1]:
            return None
        return w[2:]
    if k == 'I':
        return [mv[2], mv[2]] + w
    if k == 'K':
        if len(w) < 2 or not klein_ok(w[0], w[1]):
            return None
        return [mul(w[0], w[1])] + w[2:]
    if k == 'Ki':
        x, y = mv[2], mv[3]
        if not w or not klein_ok(x, y) or mul(x, y) != w[0]:
            return None
        return [x, y] + w[1:]
    raise ValueError(k)


def step(mv, w):
    i = mv[1]
    if i > len(w):
        return None
    r = local(mv, w[i:])
    return None if r is None else w[:i] + r


def run(moves, w):
    w = list(w)
    for mv in moves:
        w = step(mv, w)
        if w is None:
            return None
    return w


# ---------------------------------------------------------------- PhiQ

def dt(a, b, c, d):
    return from_pairs([(a, b), (c, d)])


def cf(delta):
    moved = sorted(i for i in N8 if delta[i] != i)
    a = moved[0]
    b = delta[a]
    c = min(i for i in moved if i not in (a, b))
    d = delta[c]
    rest = sorted(set(N8) - set(moved))
    rho = [(rest[0], rest[1]), (rest[2], rest[3])]
    al = from_pairs([(a, c), (b, d)] + rho)
    be = from_pairs([(a, d), (b, c)] + rho)
    assert tuple(be[al[i]] for i in N8) == delta
    return [IDX[al], IDX[be]]


AUX = (6, 7)


def phiD(c, d):
    if d >= 2:
        return [dt(0, 1, d, d + 1)]
    x = dt(1, 2, *AUX)
    y = dt(0, 1, *AUX)
    return [x, y] if not c else [y, x]


def phiQ(c, d):
    out = []
    for z in phiD(c, d):
        out += cf(z)
    return out


def phiQs(word):
    out = []
    for c, d in word:
        out += phiQ(c, d)
    return out


SYMS = [(c, d) for c in (False, True) for d in range(1, 7)]


def sym_perm(c, d):
    """The permutation of f (γ c d): s_d then s_0 (c false), s_0 then s_d."""
    def sp(k, i):
        return k + 1 if i == k else (k if i == k + 1 else i)
    if not c:
        return tuple(sp(0, sp(d, i)) for i in N8)
    return tuple(sp(d, sp(0, i)) for i in N8)


def word_perm(labels):
    """The permutation of Xs labels on the upper half: the first label
    acts first."""
    p = list(N8)
    for z in labels:
        t = TBL[z]
        p = [t[x] for x in p]
    return tuple(p)


def sym_word_perm(word):
    p = list(N8)
    for c, d in word:
        s = sym_perm(c, d)
        p = [s[x] for x in p]
    return tuple(p)


for _c, _d in SYMS:
    assert word_perm(phiQ(_c, _d)) == sym_perm(_c, _d), (_c, _d)


# ---------------------------------------------------------------- relations

def rs_relations():
    """EvenRS 8's relations in the order of its constructors, with the
    words of symbols on both sides."""
    R = []
    for c in (False, True):
        for d in range(1, 7):
            R.append((('order', c, d), [(c, d), (not c, d)], []))
        R.append((('braid0', c), [(not c, 1)], [(c, 1), (c, 1)]))
        for d in range(1, 6):
            R.append((('braid', c, d), [(c, d), (not c, d + 1), (c, d)], [(c, d + 1), (not c, d), (c, d + 1)]))
        for e in range(2, 7):
            R.append((('far0', c, e), [(c, e)], [(not c, e)]))
        for d in range(1, 7):
            for e in range(d + 2, 7):
                R.append((('far', c, d, e), [(c, d), (not c, e)], [(c, e), (not c, d)]))
    return R


def remap(mv):
    k = mv[0]
    if k == 'I':
        return ('I', mv[1], IDX[mv[2]])
    if k == 'Ki':
        return ('Ki', mv[1], IDX[mv[2]], IDX[mv[3]])
    return (k, mv[1])


def relation_certificates():
    import certgen
    out = []
    for name, l, r in rs_relations():
        L = [z for s in l for z in certgen.PhiD(s)]
        Rr = [z for s in r for z in certgen.PhiD(s)]
        assert [IDX[m] for m in certgen.pmw(L)] == phiQs(l), name
        assert [IDX[m] for m in certgen.pmw(Rr)] == phiQs(r), name
        dpath = certgen.dsearch(L, Rr)
        assert dpath is not None, name
        moves, w = certgen.expand(L, dpath)
        moves = [remap(m) for m in moves]
        lw, rw = phiQs(l), phiQs(r)
        assert run(moves, lw) == rw, name
        assert sym_word_perm(l) == sym_word_perm(r)
        out.append((name, l, r, lw, rw, moves))
    return out


# ---------------------------------------------------------------- rev

def bfs(a, b, maxlen=6):
    a, b = tuple(a), tuple(b)
    if a == b:
        return []
    prev = {a: None}
    dq = deque([a])
    while dq:
        w = dq.popleft()
        cand = []
        for i in range(len(w) - 1):
            cand += [('H', i), ('Hi', i), ('C', i), ('K', i)]
        for mv in cand:
            v = step(mv, list(w))
            if v is None or len(v) > maxlen:
                continue
            v = tuple(v)
            if v in prev:
                continue
            prev[v] = (w, mv)
            if v == b:
                path = []
                u = v
                while prev[u] is not None:
                    path.append(prev[u][1])
                    u = prev[u][0]
                return list(reversed(path))
            dq.append(v)
    return None


def rev_certificates():
    out = {}
    for c, d in SYMS:
        a = list(reversed(phiQ(c, d)))
        b = phiQ(not c, d)
        p = bfs(a, b)
        assert p is not None and run(p, a) == b, (c, d)
        out[(c, d)] = p
    return out


# ---------------------------------------------------------------- closure

def star(ws, nu):
    for m in reversed(ws):
        nu = c3(m, nu)
    return nu


def conjs_ok(ws, nu):
    """conj-ok at each step of star, outermost first."""
    ok = True
    acc = nu
    for m in reversed(ws):
        ok = ok and conj_ok(m, acc)
        acc = c3(m, acc)
    return ok


BASE_SYMS = [(False, 2), (False, 4), (False, 6)]
# Found by the design search (scratchpad), on matchings; replayed below.
BASE_MOVES = [('H', 3), ('Hi', 2), ('H', 3), ('C', 4), ('H', 1), ('K', 0), ('K', 1), ('K', 0)]


def closure():
    lw = phiQs(BASE_SYMS)
    assert run(BASE_MOVES, lw) == [MU0_IDX]
    par = {MU0_IDX: (MU0_IDX, (False, 1), 0)}
    dq = deque([MU0_IDX])
    while dq:
        m = dq.popleft()
        for x in SYMS:
            ws = phiQ(*x)
            m2 = star(ws, m)
            if m2 not in par:
                assert conjs_ok(ws, m), (x, m)
                par[m2] = (m, x, par[m][2] + 1)
                dq.append(m2)
    assert len(par) == 105
    return par


def psi(par, m):
    p, x, dep = par[m]
    if dep == 0:
        return list(BASE_SYMS)
    xi = (not x[0], x[1])
    return [x] + psi(par, p) + [xi]


if __name__ == '__main__':
    certs = relation_certificates()
    print('54 relation certificates: %d moves, max %d' %
          (sum(len(c[5]) for c in certs), max(len(c[5]) for c in certs)))
    revs = rev_certificates()
    print('rev certificates: max %d moves' % max(len(p) for p in revs.values()))
    par = closure()
    print('closure: depth %d' % max(v[2] for v in par.values()))
    for m in range(105):
        w = psi(par, m)
        assert sym_word_perm(w) == PMS[m], m
    print('psi realises every label: OK')
