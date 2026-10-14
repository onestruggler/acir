# The same-pair calculus at the canonical pair (target 0, controls 1 2 3
# black): C(w) = [T, Lambda_3(w_0)] for a target word w, T = Toff(0;1,2).
#   C(S) = PP (the gadget, literally), C(U') = eps for U' = K^-1 S K,
#   the cocycle C(v w) = C(v) . Lambda(v) C(w) Lambda(v)^-1, and the
#   controlled action Lambda(v) g Lambda(v)^-1 = g with v on its target.
# From the exact braid S U' S = U' S U' the core product relation
#   REL0:  PP . Gad(S U') = Gad(U')      (L(iZ) L(iX) = L(-iY))
# and from it, by conjugation, every product relation of gadgets on one pair.
from deriv import Derivation, show, norm, inv
import passes as P
from passes import L
import gadgetlib as G
from gadgetlib import Gad, lam, winv, wnorm, ca
from blocks import BD

t, c = 0, 3
T = ('TOFF', 0, 1, 2)
D = ('CCZ', 0, 1, 2)
def lamw(w): return [lam(c, t, x)[0] for x in w]
def Cw(w): return norm([T] + lamw(w) + [T] + lamw(winv(w)))
US = ['Kd', 'S', 'K']                                  # U' = K^-1 S K
a = G.core(0, 1)
assert norm(Cw(['S'])) == a

def C_triv():
    name = "C(U')=eps"
    if name in L: return name
    bd = BD(name, [[T], lamw(US), [T], lamw(winv(US))], [])
    bd.win(1, 1, [[('Kd', 0)], [('CS', 0, 3)], [('K', 0)]])
    bd.win(5, 1, [[('Kd', 0)], [('CSd', 0, 3)], [('K', 0)]])
    # T Kd CS K T Kd CSd K
    bd.win(0, 2, [[('Kd', 0)], [D]])                    # T Kd -> Kd D
    bd.win(3, 3, [[D]])                                  # K T Kd -> D
    bd.swap(1, P.prove([(D,)], [(('CS', 0, 3),)]))      # D CS -> CS D
    bd.win(2, 2, [])                                     # D D
    bd.win(1, 2, [])                                     # CS CSd
    bd.win(0, 2, [])                                     # Kd K
    return bd.done()

def cocycle(v, w):
    name = f'cocycle {"".join(v)}|{"".join(w)}'
    if name in L: return name
    rhs = Cw(v) + lamw(v) + Cw(w) + lamw(winv(v))
    d = Derivation(name, Cw(v + w), rhs, L)
    p = 1 + len(v)
    d.win(p, p, [T, T])
    d.win(p + 1, p + 1, lamw(winv(v)) + lamw(v))
    d.done(); return name

def caw(v, g):
    """Lambda(v) g Lambda(v)^-1 -> g with v on its target."""
    out = Gad(g.t, g.W, list(v) + list(g.d), g.e)
    name = f'CAw {"".join(v)} {g!r}'
    if name in L: return name, out
    d = Derivation(name, lamw(v) + g.letters() + lamw(winv(v)), out.letters(), L)
    cur = g; k = len(v)
    for i in range(k - 1, -1, -1):
        nm, g2 = ca(c, v[i], cur)
        d.lemma(nm, i)                                   # Lam(v_i) g -> g' Lam(v_i)
        p = i + len(g2.letters())
        d.win(p, p + 2, [])                              # Lam(v_i) Lam(v_i)^-1
        cur = g2
    d.done(); return name, out

def L1():
    """C(S U' S) -> a . Gad(S U')."""
    name = "C(SU'S)"
    if name in L: return name
    v = ['S'] + US + ['S']
    gU = Gad(0, (), US, 1); gSU = Gad(0, (), ['S'] + US, 1)
    bd = BD(name, [Cw(v)], a + gSU.letters())
    bd.lem(0, 1, [a, lamw(['S']), Cw(US + ['S']), lamw(['Sd'])], cocycle(['S'], US + ['S']))
    bd.lem(2, 1, [Cw(US), lamw(US), a, lamw(winv(US))], cocycle(US, ['S']))
    bd.lem(2, 1, [], C_triv())
    nm, _ = caw(US, Gad(0)); bd.lem(2, 3, [gU.letters()], nm)
    nm, _ = caw(['S'], gU); bd.lem(1, 3, [gSU.letters()], nm)
    return bd.done()

def L2():
    """C(U' S U') -> Gad(U')."""
    name = "C(U'SU')"
    if name in L: return name
    v = US + ['S'] + US
    gU = Gad(0, (), US, 1)
    bd = BD(name, [Cw(v)], gU.letters())
    bd.lem(0, 1, [Cw(US), lamw(US), Cw(['S'] + US), lamw(winv(US))], cocycle(US, ['S'] + US))
    bd.lem(0, 1, [], C_triv())
    bd.lem(1, 1, [a, lamw(['S']), Cw(US), lamw(['Sd'])], cocycle(['S'], US))
    bd.lem(3, 1, [], C_triv())
    bd.win(2, 2, [])                                      # Lam(S) Lam(S)^-1
    nm, _ = caw(US, Gad(0)); bd.lem(0, 3, [gU.letters()], nm)
    return bd.done()

def REL0():
    name = 'REL0'
    if name in L: return name
    gU = Gad(0, (), US, 1); gSU = Gad(0, (), ['S'] + US, 1)
    v1 = ['S'] + US + ['S']; v2 = US + ['S'] + US
    bd = BD(name, [a, gSU.letters()], gU.letters())
    bd.lem(0, 2, [Cw(v1)], L1(), fwd=False)
    o = 1                                                 # Lam(S U' S) -> Lam(U' S U'), both places
    d = bd.d
    d.win(1, 1 + len(v1), lamw(v2))
    q = 2 + len(v2)
    d.win(q, q + len(v1), lamw(winv(v2)))
    bd.b = [Cw(v2)]
    bd.lem(0, 1, [gU.letters()], L2())
    return bd.done()

if __name__ == '__main__':
    print(REL0(), 'ok')

# ------------------------------------------------------------ 2 x 2 matrices of target words
import cmath
_I = 1j
_g = 1 + 1j
M1 = {'S': ((1, 0), (0, _I)), 'Sd': ((1, 0), (0, -_I)),
      'K': ((1 / _g, 1 / _g), (1 / _g, -1 / _g))}
def _mm(A, B): return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def _inv2(A):
    det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
    return ((A[1][1] / det, -A[0][1] / det), (-A[1][0] / det, A[0][0] / det))
M1['Kd'] = _inv2(M1['K'])
def mat(w):
    R = ((1, 0), (0, 1))
    for x in w: R = _mm(R, M1[x])
    return R
IZ = ((_I, 0), (0, -_I))
def qof(d, e):
    """the 2 x 2 matrix d (iZ)^e d^-1 of Gad(d, e)."""
    m = mat(d); z = IZ if e == 1 else _inv2(IZ)
    return _mm(_mm(m, z), _inv2(m))
def close(A, B): return all(abs(A[i][j] - B[i][j]) < 1e-9 for i in range(2) for j in range(2))

# ------------------------------------------------------------ re-spelling a gadget
from deriv import fp
E = ('CCZ', 1, 2, 3)
X0 = ('X', 0)

def _diag_word(s):
    """letters (S/Sd on 0 and scalars) equal to the one-wire word s."""
    tgt = fp([(x, 0) for x in s])
    for j in range(4):
        for k in range(4):
            z = [('S', 0)] * j + [('iI',)] * k
            if fp(z) == tgt: return z
    raise ValueError(('not diagonal', s))

def _s_pass(z, e):
    """each letter of z passes core(0, e)."""
    cl = G.core(0, e)
    out = []
    for g in z:
        if g[0] == 'S': out.append(P.prove([(g,)], P.units(cl)))
        else: out.append(None)
    return out

def spell(g, g2):
    """g -> g2, the same gate on the same pair (target 0, colours W)."""
    assert g.t == g2.t == 0 and g.W == g2.W
    assert close(qof(g.d, g.e), qof(g2.d, g2.e)), (g, g2)
    name = f'spell {g!r} -> {g2!r}'
    if name in L or g.letters() == g2.letters(): return name if name in L else None
    s = wnorm(winv(list(g2.d)) + list(g.d))           # g.d = g2.d s
    k = len(g.W)
    d = Derivation(name, g.letters(), g2.letters(), L)
    dl = [(x, 0) for x in g.d]; d2 = [(x, 0) for x in g2.d]
    sl = [(x, 0) for x in s]
    d.win(k, k + len(dl), d2 + sl)
    cl = G.core(0, g.e)
    p = k + len(d2) + len(sl) + len(cl)
    idl = [(x, 0) for x in winv(list(g.d))]
    d.win(p, p + len(idl), [(x, 0) for x in winv(s)] + [(x, 0) for x in winv(list(g2.d))])
    q = k + len(d2)                                    # s core s^-1 at q
    flip = not close(qof(s, 1), IZ)
    if flip:
        z = _diag_word(wnorm(XW_ + s)) if False else None
    # write s = X^f z with z diagonal
    zs = wnorm((['K', 'S', 'S', 'Kd'] if flip else []) + s)    # X^f s, diagonal
    z = _diag_word(zs)
    xs_ = [X0] if flip else []
    d.win(q, q + len(sl), xs_ + z)
    pz = q + len(xs_)
    for i in range(len(z) - 1, -1, -1):                # z past the core
        g_ = z[i]; at = pz + i
        if g_[0] == 'S': d.lemma(P.prove([(g_,)], P.units(cl)), at)
        else:
            for j in range(len(cl)): d.comm(at + j)
    # now X^f core z z^-1 X^f ...: cancel z with s^-1's diagonal part
    p2 = q + len(xs_) + len(cl)
    zi = inv(z)
    d.win(p2, p2 + len(z) + len(sl), zi[:0] + xs_)      # z s^-1 -> X^f   (on wire 0)
    if flip:
        lem = 'PP-flip' if g.e == 1 else G.inv_lemma('PP-flip')
        d.lemma(lem, q)
    d.done(); return name

def phase_free(g, g2):
    """spell(g, g2) needs no scalar letter."""
    s = wnorm(winv(list(g2.d)) + list(g.d))
    flip = not close(qof(s, 1), IZ)
    zs = wnorm((['K', 'S', 'S', 'Kd'] if flip else []) + s)
    tgt = fp([(x, 0) for x in zs])
    return any(fp([('S', 0)] * j) == tgt for j in range(4))

# ------------------------------------------------------------ products on one pair
def REL(u):
    """Gad(u) Gad(u S U') -> Gad(u U')."""
    u = wnorm(list(u))
    g1, g2, g3 = Gad(0, (), u, 1), Gad(0, (), u + ['S'] + US, 1), Gad(0, (), u + US, 1)
    name = f'REL {"".join(u)}'
    if name in L: return name, g1, g2, g3
    r0 = REL0()
    h2, h3 = Gad(0, (), ['S'] + US, 1), Gad(0, (), US, 1)
    d = Derivation(name, g1.letters() + g2.letters(), g3.letters(), L)
    ul = [(x, 0) for x in u]; ui = [(x, 0) for x in winv(u)]
    p = len(ul) + len(a)
    m = len(ui) + len(g2.d)
    d.win(p, p + m, [(x, 0) for x in h2.d])            # u^-1 (u S U') -> S U'
    p2 = p + len(h2.d) + len(a)
    d.win(p2, p2 + len(g2.d), [(x, 0) for x in winv(list(h2.d))] + ui)
    d.lemma(r0, len(ul))
    d.win(0, len(ul) + len(h3.d), [(x, 0) for x in g3.d])
    q = len(g3.d) + len(a)
    d.win(q, q + len(h3.d) + len(ui), [(x, 0) for x in winv(list(g3.d))])
    d.done(); return name, g1, g2, g3

def prod(g1, g2):
    """(lemma, g3): g1 g2 -> g3 for two gadgets on the canonical pair on different axes."""
    q1, q2 = qof(g1.d, g1.e), qof(g2.d, g2.e)
    for u in W1.values():
        if close(qof(u, 1), q1) and close(qof(list(u) + ['S'] + US, 1), q2):
            break
    else: raise ValueError(('prod: same axis', g1, g2))
    nm, h1, h2, h3 = REL(u)
    name = f'prod {g1!r} {g2!r}'
    if name in L: return name, h3
    d = Derivation(name, g1.letters() + g2.letters(), h3.letters(), L)
    s1 = spell(g1, h1)
    if s1: d.lemma(s1, 0)
    s2 = spell(g2, h2)
    if s2: d.lemma(s2, len(h1.letters()))
    d.lemma(nm, 0)
    d.done(); return name, h3

W1 = G.W1
XW_ = G.XW
