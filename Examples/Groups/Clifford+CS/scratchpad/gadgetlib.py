# The gadget layer: fully controlled target gates at four wires as
# target-conjugates of the phase gadget, and the controlled action.
#
# A gadget Gad(t, W, d, e) is  X_W . d . PP_t^e . d^-1 . X_W : the phase
# gadget PP_t = L(iZ_t) on target t (controls the other three wires,
# canon(t)), conjugated by the target word d (letters S, Sd, K, Kd on t),
# inverted when e = -1, and coloured white on the controls W.  It acts on
# the target as d (iZ)^e d^-1 where every control has its colour, and
# trivially elsewhere.
#
# The controlled action, from the rule ck-tct: a target gate controlled
# white by a black control of a gadget passes it (nc_pass), so a target
# gate controlled black by it acts on the gadget as the bare gate (ca).
from deriv import Derivation, show, fp, cczs, norm, inv
import passes as P
from passes import L
import lib4
import gadgets4
from gadgets4 import canon, form

# ------------------------------------------------------------ one-qubit words
# The group <S, K> (order 96, phases included): every element as a
# shortest word over S, Sd, K, Kd, by breadth-first search on its action.
from prover2 import apply as _apply, VECS as _VECS
def _fp1(word):
    out = []
    for v in _VECS:
        for g in reversed(word): v = _apply((g, 0), v)
        out.extend(v)
    return tuple(out)

def _words1():
    best = {_fp1([]): []}; frontier = [[]]
    while frontier:
        nxt = []
        for w in frontier:
            for g in ('S', 'Sd', 'K', 'Kd'):
                w2 = w + [g]; k = _fp1(w2)
                if k not in best: best[k] = w2; nxt.append(w2)
        frontier = nxt
    return best
W1 = _words1()
assert len(W1) == 96, len(W1)
INV1 = {'S': 'Sd', 'Sd': 'S', 'K': 'Kd', 'Kd': 'K'}
def winv(w): return [INV1[g] for g in reversed(w)]
def wnorm(w): return list(W1[_fp1(w)])            # shortest spelling of the element

# ------------------------------------------------------------ gadgets
class Gad:
    def __init__(self, t, W=(), d=(), e=1):
        self.t, self.W, self.d, self.e = t, tuple(sorted(W)), tuple(wnorm(list(d))), e
    def letters(self):
        xs = [('X', w) for w in self.W]
        ds = [(g, self.t) for g in self.d]
        return xs + ds + core(self.t, self.e) + [(g, self.t) for g in winv(list(self.d))] + xs
    def controls(self): return [w for w in range(4) if w != self.t]
    def __repr__(self): return f'Gad(t={self.t}, W={self.W}, d={"".join(self.d) or "1"}, e={self.e})'

def gunits(g): return [tuple(g.letters())]

def core(t, e):
    """PP_t^e, spelled as the pass lemmas spell it."""
    b = norm(canon(t))
    return b if e == 1 else inv(b)

# ------------------------------------------------------------ the rule at the gadget
def lam(c, t, g):
    """Lambda_c(g_t) as macro letters: g in S Sd K Kd."""
    return {'S': [('CS', c, t)], 'Sd': [('CSd', c, t)], 'K': [('CK', c, t)], 'Kd': [('CKd', c, t)]}[g]

def nc_unit(c, t, g):
    """Lambda_not-c(g_t) = X_c Lambda_c(g_t) X_c, as one unit."""
    return tuple([('X', c)] + lam(c, t, g) + [('X', c)])

def rule_at(t, c):
    """X_c CK(c,t) X_c passes canon(t)."""
    A = [nc_unit(c, t, 'K')]
    name = P.pname(A, P.units(norm(canon(t))))
    if name in L: return name
    f = form(t, c); base = norm(canon(t))
    d = Derivation(name, P.flat(A) + base, base + P.flat(A), L)
    if f != base:
        lem = [l for (fw, l) in P.FORMS[tuple(base)] if P.flat(fw) == f][0]
        d.lemma(lem, 3)
    d.ckt(0)                                         # T C T  X_c CK X_c  Cd
    d.win(3, 7, [f[3]] + P.flat(A))                  # X_c CK X_c passes Cd (window on {c, t})
    if f != base: d.lemma(lem, 0, forward=False)
    d.done(); return name

def nc_pass_pp(c, t, g):
    """Lambda_not-c(g_t) passes canon(t), g in S Sd K Kd."""
    A = [nc_unit(c, t, g)]; B = P.units(norm(canon(t)))
    n, fwd = P.lookup(A, B)
    if n is not None: return n
    if g == 'K': return rule_at(t, c)
    if g == 'Kd':
        rule_at(t, c); return P.inverse_pass(A, B)
    return P.prove(A, B)                              # diagonal: the engine

def pass_inv_B(A, B):
    """A passes inv(B) from A passes B."""
    fA, fB = P.flat(A), P.flat(B)
    n0, fwd = P.lookup(A, B)
    if n0 is None: n0, fwd = P.prove(A, B), True
    Bi = [tuple(inv(fB))]
    name = P.pname(A, Bi)
    if name in L: return name
    iB = inv(fB)
    d = Derivation(name, fA + iB, iB + fA, L)
    P.insert_inverse(d, 0, iB)                        # iB B A iB  (iB inv(iB) = iB B)
    d.lemma(n0, len(iB), forward=not fwd)             # iB A B iB
    P.cancel_inverse(d, len(iB) + len(fA), fB)
    d.done(); return name

if __name__ == '__main__':
    for t in range(4):
        for c in range(4):
            if c == t: continue
            for g in ('K', 'Kd', 'S', 'Sd'):
                nc_pass_pp(c, t, g)
    print('rule at every target and control: ok')

# ------------------------------------------------------------ the controlled action
def tl(word, t): return [(g, t) for g in word]          # one-qubit word as letters on t

def ncu_units(c, t, word):
    return [nc_unit(c, t, x) for x in word]


def core_pass(c, t, x, e):
    """nc_unit(c,t,x) passes the core PP_t^e."""
    A = [nc_unit(c, t, x)]
    n0 = nc_pass_pp(c, t, x)
    if e == 1: return n0
    return pass_inv_B(A, P.units(norm(canon(t))))

def nc_pass(c, x, g):
    """Lambda_not-c(x_t) passes the gadget g (c a black control of g)."""
    t = g.t; assert c != t and c not in g.W
    U = nc_unit(c, t, x)
    name = P.pname([U], [tuple(g.letters())])
    if name in L: return name
    gl = g.letters(); k = len(g.W); dl = tl(g.d, t)
    v = wnorm(winv(list(g.d)) + [x] + list(g.d))
    V = ncu_units(c, t, v); Vf = P.flat(V)
    d = Derivation(name, list(U) + gl, gl + list(U), L)
    for j in range(k):                                   # U past X_W (a window on three wires)
        d.win(j, j + 4, [gl[j]] + list(U))
    pos = k
    d.win(pos, pos + 3 + len(dl), dl + Vf)               # U d -> d V   (window on {c, t})
    p = pos + len(dl); cl = core(t, g.e)
    # each V unit passes the core, last first
    for i in range(len(V) - 1, -1, -1):
        q = p + 3 * i
        d.lemma(core_pass(c, t, v[i], g.e), q)
    p2 = p + len(cl)
    d.win(p2, p2 + len(Vf) + len(dl), tl(winv(list(g.d)), t) + list(U))   # V d^-1 -> d^-1 U
    q = p2 + len(dl)
    for j in range(k):
        d.win(q + j, q + j + 4, [gl[len(gl) - k + j]] + list(U))
    d.done(); return name

def ca(c, x, g):
    """Lambda_c(x_t) g = g' Lambda_c(x_t), g' = Gad(t, W, x d, e), c black in g.
    Returns (lemma name, g')."""
    t = g.t
    g2 = Gad(t, g.W, [x] + list(g.d), g.e)
    lamw = lam(c, t, x); gl, gl2 = g.letters(), g2.letters()
    name = f'CA {show(lamw)} {g!r}'
    if name in L: return name, g2
    xi = INV1[x]; U = nc_unit(c, t, xi)
    d = Derivation(name, lamw + gl, gl2 + lamw, L)
    d.win(0, 1, [(x, t)] + list(U))                       # Lambda_c(x) = x_t . Lambda_not-c(x^-1)
    d.lemma(nc_pass(c, xi, g), 1)                         # x_t g U
    k = len(g.W); n = len(gl)
    for j in range(k): d.comm(j)                          # x_t past X_W
    dl, dl2 = tl(g.d, t), tl(g2.d, t)
    d.win(k, k + 1 + len(dl), dl2)                        # x d -> d'
    p = k + len(dl2) + len(core(t, g.e))
    d.win(p, p + len(dl), tl(winv(list(g2.d)), t) + [(x, t)])   # d^-1 -> d'^-1 x
    q = p + len(dl2)
    for j in range(k): d.comm(q + j)                      # x_t past the trailing X_W
    d.win(len(gl2), len(gl2) + 4, lamw)                   # x_t U -> Lambda_c(x)
    d.done(); return name, g2

# ------------------------------------------------------------ forms of the core
def inv_lemma(name):
    """from X -> Y, the lemma inv(X) -> inv(Y)."""
    nm = name + ' ^-1'
    if nm in L: return nm
    X, Y = L[name]; iX, iY = inv(list(X)), inv(list(Y))
    d = Derivation(nm, iX, iY, L)
    P.insert_inverse(d, len(iX), list(Y))              # iX Y iY
    d.lemma(name, len(iX), forward=False)              # iX X iY
    P.cancel_inverse(d, 0, iX)                         # iY
    d.done(); return nm

def form_lemma(t, k, e):
    """(lemma, form) with core(t, e) -> form, CS taken from k."""
    base = norm(canon(t)); f = form(t, k)
    if f == base: return None, core(t, e)
    lem = [l for (fw, l) in P.FORMS[tuple(base)] if P.flat(fw) == f][0]
    if e == 1: return lem, f
    return inv_lemma(lem), norm(inv(f))

def xs(W): return [('X', w) for w in sorted(W)]

# ------------------------------------------------------------ a unit on a control
def core_pass_ctl(c, w, x, t, e):
    """nc_unit(c, w, x) passes core(t, e), w a control (the core black on c, w)."""
    U = nc_unit(c, w, x); cl = core(t, e)
    name = P.pname([U], P.units(cl))
    if name in L: return name
    z = [v for v in range(4) if v not in (c, w, t)][0]
    lem, f = form_lemma(t, z, e)
    d = Derivation(name, list(U) + cl, cl + list(U), L)
    if lem: d.lemma(lem, 3)
    inner = P.prove([U], P.units(f))
    d.lemma(inner, 0)
    if lem: d.lemma(lem, 0, forward=False)
    d.done(); return name

XW = ['K', 'S', 'S', 'Kd']                             # X = K Z K^-1, exactly

def opp_pass(c, w, x, g):
    """Lambda_not-c(x_w) passes g, c a black control of g, w any wire but c."""
    t = g.t; assert c != t and c not in g.W and w != c
    U = nc_unit(c, w, x); gl = g.letters()
    name = P.pname([U], [tuple(gl)])
    if name in L: return name
    if w == t: return nc_pass(c, x, g)
    k = len(g.W)
    v = wnorm(XW + [x] + XW) if w in g.W else [x]
    Us = ncu_units(c, w, v); Uf = P.flat(Us)
    d = Derivation(name, list(U) + gl, gl + list(U), L)
    d.win(0, 3 + k, gl[:k] + Uf)                        # U past X_W, X-conjugated on w
    dl = tl(g.d, t)
    d.win(k, k + len(Uf) + len(dl), dl + Uf)            # the units past d (a window on {c, w, t})
    p = k + len(dl)
    cl = core(t, g.e)
    for i in range(len(v) - 1, -1, -1):
        q = p + 3 * i
        d.lemma(core_pass_ctl(c, w, v[i], t, g.e), q)
    p2 = p + len(cl)
    idl = tl(winv(list(g.d)), t)
    d.win(p2, p2 + len(Uf) + len(idl), idl + Uf)
    q = p2 + len(idl)
    d.win(q, q + len(Uf) + k, gl[len(gl) - k:] + list(U))   # back past X_W
    d.done(); return name

def sort_xs(d, pos, have, want):
    """bubble the X letters at pos .. into the order want (X's commute)."""
    cur = list(have)
    for i in range(len(want)):
        j = cur.index(want[i], i)
        while j > i:
            d.comm(pos + j - 1); cur[j - 1], cur[j] = cur[j], cur[j - 1]; j -= 1

def blk_pass(c, w, x, g):
    """Lambda_c(x_w) (one letter) passes g, c a white control of g."""
    t = g.t; assert c in g.W and w != c
    gb = Gad(t, [v for v in g.W if v != c], g.d, g.e)
    lw = lam(c, w, x); gl, gbl = g.letters(), gb.letters()
    name = P.pname([tuple(lw)], [tuple(gl)])
    if name in L: return name
    inner = opp_pass(c, w, x, gb)
    k = len(g.W); n = len(gl)
    d = Derivation(name, lw + gl, gl + lw, L)
    sort_xs(d, 1, xs(g.W), [('X', c)] + xs(gb.W))       # Lam X_c X_W' ...
    d.win(0, 2, [('X', c)] + list(nc_unit(c, w, x)))      # X_c (X_c Lam X_c) X_W' ...
    sort_xs(d, n - k + 3, xs(g.W), xs(gb.W) + [('X', c)])  # ... X_W' X_c
    d.lemma(inner, 1)                                    # X_c gb U X_c
    q = 1 + len(gbl)
    d.win(q, q + 4, [('X', c)] + lw)                     # U X_c -> X_c Lam
    # X_c gb X_c Lam: put the X's back in order
    sort_xs(d, 0, [('X', c)] + xs(gb.W), xs(g.W))
    q = len(gl) - k
    sort_xs(d, q, xs(gb.W) + [('X', c)], xs(g.W))
    d.done(); return name

def unit_pass(c, w, x, black, g):
    """the unit Lambda_c(x_w) (black) or Lambda_not-c(x_w) passes g of the other colour on c."""
    return blk_pass(c, w, x, g) if black else opp_pass(c, w, x, g)

# ------------------------------------------------------------ splitting off the target word
def colour(g, c): return c not in g.W                   # True: black on c

def cunit(c, w, x, black):
    return tuple(lam(c, w, x)) if black else nc_unit(c, w, x)

def ca_split(g, c):
    """g -> Lambda(d) g0 Lambda(d)^-1, Lambda of g's own colour on c, g0 = g with d = ().
    Returns (lemma, units of Lambda(d), g0)."""
    t = g.t; blk = colour(g, c)
    g0 = Gad(t, g.W, (), g.e)
    if not g.d: return None, [], g0
    sm = [cunit(c, t, y, blk) for y in g.d]
    smi = [cunit(c, t, INV1[y], blk) for y in reversed(g.d)]
    op = [cunit(c, t, y, not blk) for y in g.d]
    opi = [cunit(c, t, INV1[y], not blk) for y in reversed(g.d)]
    name = f'ca-split {g!r} {c}'
    gl, g0l = g.letters(), g0.letters()
    rhs = P.flat(sm) + g0l + P.flat(smi)
    if name in L: return name, sm, g0
    d = Derivation(name, gl, rhs, L)
    k = len(g.W); dl = tl(g.d, t); idl = tl(winv(list(g.d)), t)
    # X_W past d, and d^-1 past X_W (disjoint letters)
    for i in range(len(dl)):
        for j in range(k - 1, -1, -1): d.comm(i + j)
    # move the X_W block at the end leftwards past d^-1: bubble each X left
    pos = len(gl) - k
    for j in range(k):
        for i in range(len(idl)):
            d.comm(pos + j - 1 - i)
    # now: d X_W core X_W d^-1
    d.win(0, len(dl), P.flat(sm) + P.flat(op))             # d -> Lam_same(d) Lam_opp(d)  (on {c, t})
    e = len(P.flat(sm)) + len(P.flat(op)) + len(g0l)
    d.win(e, e + len(idl), P.flat(opi) + P.flat(smi))      # d^-1 -> Lam_opp(d)^-1 Lam_same(d)^-1
    p = len(P.flat(sm))
    for i in range(len(op) - 1, -1, -1):                    # Lam_opp units past g0
        q = p + len(P.flat(op[:i]))
        d.lemma(unit_pass(c, t, g.d[i], not blk, g0), q)
        # the unit now sits after g0, before the units already moved
    # cancel Lam_opp(d) Lam_opp(d)^-1 (a window on {c, t})
    q = p + len(g0l)
    d.win(q, q + len(P.flat(op)) + len(P.flat(opi)), [])
    d.done(); return name, sm, g0

# ------------------------------------------------------------ separated gadgets
def gu(g):
    """g with d = () in the engine's format."""
    assert not g.d
    u = P.units(core(g.t, g.e))
    return [P.Col(list(g.W), u)] if g.W else u

def diag_pass(A0, B0):
    """lemma A0 B0 -> B0 A0 for two diagonal gadgets (d = ())."""
    a, b = gu(A0), gu(B0)
    n, fwd = P.lookup(a, b)
    if n is not None and fwd: return n
    name = P.pname(a, b)
    for (X, Y, back) in ((a, b, False), (b, a, True)):
        try:
            m = P.prove(X, Y)
            if not back: return m
            return P.done_as(name, a, b, lambda d: d.lemma(m, 0, forward=False))
        except P.Fail: pass
    # inverse cores: from the uninverted ones
    if A0.e == -1:
        m = diag_pass(Gad(A0.t, A0.W, (), 1), B0)
        return P.done_as(name, a, b, lambda d: _inv_left(d, m, A0, B0))
    if B0.e == -1:
        m = diag_pass(A0, Gad(B0.t, B0.W, (), 1))
        return P.done_as(name, a, b, lambda d: _inv_right(d, m, A0, B0))
    raise P.Fail(('diag_pass', repr(A0), repr(B0)))

def ins_gad(d, k, g):
    """at k insert g . g^-1 (g^-1 = the gadget with e negated), X letters sorted."""
    gl_ = g.letters(); n = len(g.W)
    P.insert_inverse(d, k, gl_)
    q = k + len(gl_)                                      # inv(gl_) starts here, its X's reversed
    sort_xs(d, q, list(reversed(xs(g.W))), xs(g.W))
    m = q + len(gl_) - n
    sort_xs(d, m, list(reversed(xs(g.W))), xs(g.W))

def cancel_gad(d, k, g):
    """at k: g . g^-1 -> eps."""
    gl_ = g.letters(); n = len(g.W)
    q = k + len(gl_)
    sort_xs(d, q, xs(g.W), list(reversed(xs(g.W))))
    m = q + len(gl_) - n
    sort_xs(d, m, xs(g.W), list(reversed(xs(g.W))))
    P.cancel_inverse(d, k, gl_)

def ginv(g): return Gad(g.t, g.W, g.d, -g.e)

def _inv_left(d, m, A0, B0):
    """A0 = A1^-1, m: A1 B0 -> B0 A1; show A0 B0 -> B0 A0."""
    A1 = ginv(A0); a0 = A0.letters(); b0 = B0.letters()
    ins_gad(d, len(a0) + len(b0), A1)                    # A0 B0 A1 A0
    d.lemma(m, len(a0), forward=False)                  # A0 A1 B0 A0
    cancel_gad(d, 0, A0)

def _inv_right(d, m, A0, B0):
    """B0 = B1^-1, m: A0 B1 -> B1 A0; show A0 B0 -> B0 A0."""
    B1 = ginv(B0); a0 = A0.letters(); b0 = B0.letters()
    ins_gad(d, 0, B0)                                    # B0 B1 A0 B0
    d.lemma(m, len(b0), forward=False)                  # B0 A0 B1 B0
    cancel_gad(d, len(b0) + len(a0), B1)

def sep_pass(A, B, c):
    """A passes B, the two gadgets of opposite colours on c."""
    assert colour(A, c) != colour(B, c) and c not in (A.t, B.t)
    al, bl = A.letters(), B.letters()
    name = P.pname([tuple(al)], [tuple(bl)])
    if name in L: return name
    sA, smA, A0 = ca_split(A, c)
    a0l = A0.letters()
    core_name = f'pass [{show(a0l)}] [{show(bl)}]'
    if core_name not in L:
        sB, smB, B0 = ca_split(B, c)
        d = Derivation(core_name, a0l + bl, bl + a0l, L)
        if sB: d.lemma(sB, len(a0l))
        p = 0
        for u, y in zip(smB, B.d):                       # A0 u -> u A0
            d.lemma(unit_pass(c, B.t, y, colour(B, c), A0), p, forward=False); p += len(u)
        dp = diag_pass(A0, B0)
        d.lemma(dp, p); p += len(B0.letters())
        for u, y in zip([cunit(c, B.t, INV1[y], colour(B, c)) for y in reversed(B.d)], [INV1[y] for y in reversed(B.d)]):
            d.lemma(unit_pass(c, B.t, y, colour(B, c), A0), p, forward=False); p += len(u)
        if sB: d.lemma(sB, 0, forward=False)
        d.done()
    d = Derivation(name, al + bl, bl + al, L)
    if sA: d.lemma(sA, 0)
    smiA = [cunit(c, A.t, INV1[y], colour(A, c)) for y in reversed(A.d)]
    ys = [INV1[y] for y in reversed(A.d)]
    pos = len(P.flat(smA)) + len(a0l) + len(P.flat(smiA))
    for u, y in reversed(list(zip(smiA, ys))):           # u B -> B u, from the right
        pos -= len(u); d.lemma(unit_pass(c, A.t, y, colour(A, c), B), pos)
    pos -= len(a0l); d.lemma(core_name, pos)
    for u, y in reversed(list(zip(smA, A.d))):
        pos -= len(u); d.lemma(unit_pass(c, A.t, y, colour(A, c), B), pos)
    if sA: d.lemma(sA, len(bl), forward=False)
    d.done(); return name
