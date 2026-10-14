# The consecutive facts of Lemma 8.8 at n = 4 at the canonical pair
# (target 0, controls 1 2 3 black, orientation 0): the decoded letters
#   p = PP, p' = X0 PP X0, l = ROT, h = X0 ROT X0
# and the facts the generic layer asks of them on one pair.
from deriv import Derivation, show, norm, inv
import passes as P
from passes import L
import gadgetlib as G
from gadgetlib import Gad
import samepair as SP
from blocks import BD
from lemmas6 import ROT, K, Kd, U, Ui, PPi, SW13w
from lemmas5 import PP3

X0 = ('X', 0)
PP = norm(PP3)
assert PP == G.core(0, 1)
R = Gad(0, (), ['S', 'K'], -1)          # the rotation as a gadget
Ri = Gad(0, (), ['S', 'K'], 1)

def rot_gad():
    """ROT -> Gad(0, (), S K, -1)."""
    name = 'ROT-gad'
    if name in L: return name
    d = Derivation(name, ROT, R.letters(), L)
    d.lemma('ROT=[c,F]', 0); d.lemma('ROT-form', 0)
    # K SW13w U PPi Ui SW13w Kd: U left past SW13w, Ui right past it (disjoint)
    for k in range(3):
        for j in range(3): d.comm(3 + k - j)
    for k in range(3):
        for j in range(3): d.comm(13 + k - j)
    # K U [SW12 SW23 SW12] PPi [SW12 SW23 SW12] Ui Kd: unwind the swaps from the inside
    d.swapconj(6, 4, 1); d.swapconj(5, 4, 2); d.swapconj(4, 4, 1)
    lem, f = G.form_lemma(0, 1, -1)
    assert d.cur[4:8] == norm(f)
    d.lemma(lem, 4, forward=False)                       # -> core(0, -1)
    d.win(0, 4, [('S', 0), ('K', 0)])                    # K Kd S K -> S K
    d.win(6, 10, [('Kd', 0), ('Sd', 0)])                 # Kd Sd K Kd -> Kd Sd
    d.done(); return name

if __name__ == '__main__':
    rot_gad()
def F6():
    """px-conj2 at the canonical pair: p l = l p'."""
    name = 'F6 p l = l p\''
    if name in L: return name
    rg = rot_gad()
    lhs = PP + ROT; rhs = ROT + [X0] + PP + [X0]
    bd = BD(name, [PP, ROT], rhs)
    bd.lem(1, 1, [R.letters()], rg)
    n1, g1 = SP.prod(Gad(0), R)
    bd.lem(0, 2, [g1.letters()], n1)
    # the other side: ROT X0 PP X0 -> R . a^-1 -> g2
    ai = Gad(0, (), (), -1)
    n2, g2 = SP.prod(R, ai)
    s = SP.spell(g1, g2)
    if s: bd.lem(0, 1, [g2.letters()], s)
    bd.lem(0, 1, [R.letters(), ai.letters()], n2, fwd=False)
    bd.lem(1, 1, [[X0] + PP + [X0]], 'PP-flip', fwd=False)
    bd.lem(0, 1, [ROT], rg, fwd=False)
    return bd.done()

if __name__ == '__main__':
    print(F6())

# ------------------------------------------------------------ adjacent: targets 0 and 1
from deriv import relabel
X1, X2, X3 = ('X', 1), ('X', 2), ('X', 3)
T = ('TOFF', 0, 1, 2)
C3, C3d = ('CS', 0, 3), ('CSd', 0, 3)
D = ('CCZ', 0, 1, 2); E = ('CCZ', 1, 2, 3)
a0 = Gad(0); a1 = Gad(1); b = Gad(1, (), (), -1)
v = Gad(0, (3,), ['S', 'K'], -1)                         # X3 R0 X3
w = Gad(1, (2,))                                         # X2 a1 X2
MA = norm([('CSd', 1, 2), ('S', 0), T, ('Sd', 0)])        # R0 . v (three wires)
MB = norm([('CS', 0, 3), ('CCZ', 0, 1, 3)])               # a1 . w (three wires)
MBi = norm(inv(MB))

def mergeR3():
    """R0 . X3 R0 X3 -> MA."""
    name = 'merge R0'
    if name in L: return name
    d = Derivation(name, R.letters() + v.letters(), MA, L)
    n = len(R.letters())                                 # S K core^-1 Kd Sd | X3 S K core^-1 Kd Sd X3
    for j in range(2): d.comm(n + j)                     # X3 past S K
    d.win(n - 2, n + 2, [])                              # Kd Sd S K
    m = len(d.cur); d.comm(m - 2); d.comm(m - 3)         # the last X3 past Kd Sd
    ci = G.core(0, -1)
    # S K ci X3 ci X3 Kd Sd: ci X3 ci X3 = inv(X3 c X3 c) ; X3 c X3 c = c X3 c X3 (separated)
    sp = G.sep_pass(Gad(0, (3,)), Gad(0), 3)             # X3 c X3 . c -> c . X3 c X3
    li = G.inv_lemma(sp)                                 # inv: c^-1 X3 c^-1 X3 -> X3 c^-1 X3 c^-1
    d.lemma(li, 2)
    mi = G.inv_lemma('merge3')                           # inv(PP3 X3 PP3 X3) -> inv(Qm)
    d.lemma(mi, 2)
    d.win(0, len(d.cur), MA)                             # three wires {0, 1, 2}
    d.done(); return name

def mergeB():
    """a1 . X2 a1 X2 -> MB  (merge3 at target 1 over wire 2)."""
    name = 'merge a1'
    if name in L: return name
    pi = (1, 0, 3, 2)
    m = relabel('merge3', pi, L)                          # form(1,2) X2 form(1,2) X2 -> CS03 CCZ013
    lem, f = G.form_lemma(1, 2, 1)
    d = Derivation(name, a1.letters() + w.letters(), MB, L)
    k = len(a1.letters())
    if lem:
        d.lemma(lem, 0); d.lemma(lem, k + 1)
    d.lemma(m, 0)
    if d.cur != MB: d.win(0, len(d.cur), MB)
    d.done(); return name

def core_identity():
    """MB^-1 MA -> MA MB^-1 a0."""
    name = 'CI MB MA'
    if name in L: return name
    bd = BD(name, [MBi, MA], MA + MBi + a0.letters())
    bd.ins(0, MA)                                        # MA MA^-1 MB^-1 MA
    # MA^-1 MB^-1 MA -> MB^-1 a0, as a lemma on the three blocks
    inner = 'CI conj'
    if inner not in L:
        MAi = norm(inv(MA))
        d = Derivation(inner, MAi + MBi + MA, MBi + a0.letters(), L)
        # MAi = S0 T Sd0 CS12 ; MA = CSd12 S0 T Sd0
        cur = d.cur
        i12 = cur.index(('CS', 1, 2))
        # CS12 past MBi (diagonal) and cancel with CSd12
        for g in MBi:
            nm = P.prove([(('CS', 1, 2),)], [(g,)]); d.lemma(nm, d.cur.index(('CS', 1, 2)))
        j = d.cur.index(('CS', 1, 2)); d.win(j, j + 2, [])
        # S0 T Sd0 MBi S0 T Sd0: Sd0 past MBi, cancel with S0
        j = d.cur.index(('Sd', 0))
        for g in MBi:
            nm = P.prove([(('Sd', 0),)], [(g,)]); d.lemma(nm, j); j += 1
        d.win(j, j + 2, [])
        # S0 T MBi T Sd0 = S0 (T CCZ013 T)(T CSd03 T) Sd0
        j = d.cur.index(T)
        assert d.cur[j + 1:j + 3] == MBi, show(d.cur)
        d.win(j + 2, j + 2, [T, T])                       # T CCZ013 T T CSd03 T
        d.l2(j)                                          # -> CCZ013 CCZ123 T CSd03 T
        k = j + 2
        assert d.cur[k:k + 3] == [T, C3d, T], show(d.cur)
        d.win(k, k, [C3d, C3])                           # C3d C3 T C3d T = C3d PPi
        # S0 CCZ013 E C3d PPi Sd0: Sd0 left past PPi, then everything diagonal
        p = len(d.cur) - 1
        nm = P.prove([(('Sd', 0),)], P.units(G.core(0, -1)))
        d.lemma(nm, p - 4, forward=False)
        # S0 CCZ013 E C3d Sd0 PPi: S0 right past the diagonals, cancel with Sd0
        for k in range(3):
            g = d.cur[k + 1]
            d.lemma(P.prove([(('S', 0),)], [(g,)]), k)
        d.win(3, 5, [])
        # CCZ013 E C3d PPi -> CCZ013 C3d E PPi -> CCZ013 C3d PP3
        d.lemma(P.prove([(E,)], [(C3d,)]), 1)
        d.lemma(E_PPi(), 2)
        d.done()
    bd.lem(1, 3, [MBi, a0.letters()], inner)
    return bd.done()

def E_PPi():
    """E PPi -> PP3."""
    name = 'E PPi'
    if name in L: return name
    bd = BD(name, [[E], G.core(0, -1)], PP)
    bd.lem(0, 1, [PP, PP], 'PP2=E', fwd=False)
    bd.cancel(1)
    return bd.done()

def diag_mb_a0():
    """MBi a0 -> a0 MBi (diagonal)."""
    name = 'MBi a0'
    if name in L: return name
    bd = BD(name, [[g] for g in MBi] + [PP], PP + MBi)
    for i in range(len(MBi) - 1, -1, -1):
        bd.swap(i, P.prove([(MBi[i],)], P.units(PP)))
    bd.join(0, 1)
    return bd.done()

if __name__ == '__main__':
    print(mergeR3()); print(mergeB()); core_identity()

def split_b():
    """b -> w MBi."""
    name = 'split b'
    if name in L: return name
    bd = BD(name, [b.letters()], w.letters() + MBi)
    bd.ins(0, w.letters())                               # w w^-1 b
    bd.lem(1, 2, [MBi], G.inv_lemma(mergeB()))
    return bd.done()

def split_R():
    """R -> MA v^-1."""
    name = 'split R'
    if name in L: return name
    bd = BD(name, [R.letters()], MA + norm(inv(v.letters())))
    bd.ins(1, v.letters())                               # R v v^-1
    bd.lem(0, 2, [MA], mergeR3())
    return bd.done()

def pass_MBi(g, c):
    """g passes MBi, g separated on c from a1 and w."""
    name = f'pass {g!r} MBi'
    if name in L: return name
    sw = G.sep_pass(g, w, c); sa = G.sep_pass(g, a1, c)
    wi, a1i = norm(inv(w.letters())), norm(inv(a1.letters()))
    bd = BD(name, [g.letters(), MBi], MBi + g.letters())
    bd.lem(1, 1, [wi, a1i], G.inv_lemma(mergeB()), fwd=False)
    bd.swap(0, G.pass_inv_B([tuple(g.letters())], [tuple(w.letters())]))
    bd.swap(1, G.pass_inv_B([tuple(g.letters())], [tuple(a1.letters())]))
    bd.lem(0, 2, [MBi], G.inv_lemma(mergeB()))
    return bd.done()

def F7a_gad():
    """b R0 -> R0 a0 b  (b = PP_1^-1)."""
    name = 'F7a gad'
    if name in L: return name
    vi = norm(inv(v.letters()))
    bd = BD(name, [b.letters(), R.letters()], R.letters() + a0.letters() + b.letters())
    bd.lem(0, 1, [w.letters(), MBi], split_b())
    bd.lem(2, 1, [MA, vi], split_R())
    bd.lem(1, 2, [MA, MBi, a0.letters()], core_identity())
    bd.lem(1, 1, [R.letters(), v.letters()], mergeR3(), fwd=False)
    # w R v MBi a0 vi: v right past MBi and a0, cancel
    bd.swap(2, pass_MBi(v, 3))
    bd.swap(3, G.sep_pass(v, a0, 3))
    bd.cancel(4)
    bd.swap(2, diag_mb_a0())                             # w R a0 MBi
    bd.swap(0, G.sep_pass(w, R, 2)); bd.swap(1, G.sep_pass(w, a0, 2))
    bd.lem(2, 2, [b.letters()], split_b(), fwd=False)
    return bd.done()

def F7a():
    """decoded px-conj at the adjacent pair: p_{k+1} l_k = l_k p_k p_{k+1}."""
    name = 'F7a'
    if name in L: return name
    flip1 = relabel('PP-flip', (1, 0, 2, 3), L)
    p1 = L[flip1][0]
    bd = BD(name, [p1, ROT], ROT + PP + list(p1))
    bd.lem(0, 1, [b.letters()], flip1)
    bd.lem(1, 1, [R.letters()], rot_gad())
    bd.lem(0, 2, [R.letters(), a0.letters(), b.letters()], F7a_gad())
    bd.lem(2, 1, [p1], flip1, fwd=False)
    bd.lem(0, 1, [ROT], rot_gad(), fwd=False)
    return bd.done()

if __name__ == '__main__':
    print(F7a())

# ------------------------------------------------------------ the transposed adjacent case
PI01 = (1, 0, 2, 3)
ai0 = Gad(0, (), (), -1)

def core_E():
    """core -> core^-1 E  (on the canonical pair)."""
    name = 'c -> ci E'
    if name in L: return name
    bd = BD(name, [PP], G.core(0, -1) + [E])
    bd.ins(0, G.core(0, -1))                             # ci c c   (ins puts ci, inv(ci) = c)
    bd.lem(1, 2, [[E]], 'PP2=E')
    return bd.done()

def Ri_RE():
    """Ri -> R E."""
    name = 'Ri = R E'
    if name in L: return name
    d = Derivation(name, Ri.letters(), R.letters() + [E], L)
    d.lemma(core_E(), 2)                                 # S K ci E Kd Sd
    d.comm(6); d.comm(7)
    d.done(); return name

def F7a_inv():
    """b Ri -> Ri a0 b."""
    name = 'F7a gad inv'
    if name in L: return name
    bd = BD(name, [b.letters(), Ri.letters()], Ri.letters() + a0.letters() + b.letters())
    bd.lem(1, 1, [R.letters(), [E]], Ri_RE())
    bd.lem(0, 2, [R.letters(), a0.letters(), b.letters()], F7a_gad())
    bd.swap(2, P.prove(P.units(b.letters()), [(E,)]))   # b E -> E b
    bd.swap(1, P.prove(P.units(PP), [(E,)]))            # a0 E -> E a0
    bd.lem(0, 2, [Ri.letters()], Ri_RE(), fwd=False)
    return bd.done()

def same_pair_rel(name, lhs_g, rhs_g):
    """two products of gadgets on the canonical pair with the same gate, by normalising both."""
    if name in L: return name
    def norm_side(gs):
        steps = []; cur = gs[0]
        for g in gs[1:]:
            nm, cur = SP.prod(cur, g); steps.append(nm)
        return steps, cur
    sl, gl_ = norm_side(lhs_g); sr, gr = norm_side(rhs_g)
    bd = BD(name, [g.letters() for g in lhs_g], [x for g in rhs_g for x in g.letters()])
    for nm in sl: bd.lem(0, 2, [None], nm) if False else None
    cur = lhs_g[0]
    for g, nm in zip(lhs_g[1:], sl):
        _, nxt = SP.prod(cur, g); bd.lem(0, 2, [nxt.letters()], nm); cur = nxt
    s = SP.spell(gl_, gr)
    if s: bd.lem(0, 1, [gr.letters()], s)
    # unfold the right side's products in reverse
    prods = []; cur = rhs_g[0]
    for g in rhs_g[1:]:
        nm, nxt = SP.prod(cur, g); prods.append((nm, cur, g, nxt)); cur = nxt
    for nm, c0, g, nxt in reversed(prods):
        bd.lem(0, 1, [c0.letters(), g.letters()], nm, fwd=False)
        bd.join(0, 1) if False else None
        bd.b = [c0.letters(), g.letters()] + bd.b[2:]
        bd.join(0, len(bd.b) - 1) if False else None
    return bd.done()

def h_gad():
    """X0 ROT X0 -> Ri."""
    name = 'h-gad'
    if name in L: return name
    bd = BD(name, [[X0], ROT, [X0]], Ri.letters())
    bd.lem(1, 1, [R.letters()], rot_gad())
    g = Gad(0, (), G.XW + ['S', 'K'], -1)
    xsk = [(x, 0) for x in g.d]
    bd.join(0, 3)
    d = bd.d
    d.win(0, 3, xsk)
    n = len(xsk) + 4
    d.win(n, n + 3, [(x, 0) for x in G.winv(list(g.d))])
    bd.b = [g.letters()]
    bd.lem(0, 1, [Ri.letters()], SP.spell(g, Ri))
    return bd.done()

def F7b():
    """decoded: p'_k p'_{k+1} l_{k+1} = l_{k+1} p'_k  at the canonical adjacent pair."""
    name = 'F7b'
    if name in L: return name
    f7 = relabel(F7a_inv(), PI01, L)                      # a0^-1 Q -> Q a1 a0^-1   (Q = R1^-1)
    a0Ri = same_pair_rel("a0 Ri = Ri a0^-1", [a0, Ri], [Ri, ai0])
    sp1 = relabel(a0Ri, PI01, L)                          # a1 Q -> Q a1^-1
    hq = relabel(h_gad(), PI01, L)                        # X1 ROT1 X1 -> Q
    Q = L[hq][1]; qdec = L[hq][0]
    a1l, a1il = a1.letters(), norm(inv(a1.letters()))
    p0 = [X0] + PP + [X0]
    bd = BD(name, [p0, a1l, qdec], qdec + p0)
    bd.lem(0, 1, [ai0.letters()], 'PP-flip')
    bd.lem(2, 1, [Q], hq)
    bd.lem(1, 2, [Q, a1il], sp1)                          # a0i Q a1i
    bd.lem(0, 2, [Q, a1l, ai0.letters()], f7)             # Q a1 a0i a1i
    adj = G.pass_inv_B(P.units(a1l), [tuple(ai0.letters())]) if False else None
    sw = P.lookup([tuple(a1l)], [tuple(ai0.letters())])[0]
    bd.swap(1, adj_pass())                                # Q a0i a1 a1i
    bd.cancel(2)
    bd.lem(1, 1, [p0], 'PP-flip', fwd=False)
    bd.lem(0, 1, [qdec], hq, fwd=False)
    return bd.done()

def adj_pass():
    """a1 a0^-1 -> a0^-1 a1 (adjacent phase gadgets commute, adj01)."""
    name = 'a1 a0i'
    if name in L: return name
    a1l = a1.letters(); ail = ai0.letters()
    # adj01: PP_0 PP_1 -> PP_1 PP_0
    bd = BD(name, [a1l, ail], ail + a1l)
    bd.ins(0, ail)                                       # a0i a0 a1 a0i
    bd.swap(1, 'adj01')
    bd.cancel(2)
    return bd.done()

if __name__ == '__main__':
    print(F7b())

# ------------------------------------------------------------ the braid (Clement's (358))
CZ01, SW01 = ('CZ', 0, 1), ('SWAP', 0, 1)
CS01, CSd01 = ('CS', 0, 1), ('CSd', 0, 1)
F0 = norm([CZ01, SW01])
Qg = Gad(1, (), ['S', 'K'], 1)                           # the decoded l_{k+1} as a gadget

def copies(g): return [Gad(g.t, W, g.d, g.e) for W in [(3,), (2,), (2, 3)]]
def gl(gs): return [x for g in gs for x in g.letters()]

def merge_all(g, out):
    """g . (its copies white on 3, 2, 2 3) -> out (two wires {t, other}), g on the canonical pair."""
    name = f'merge-all {g!r}'
    if name in L: return name
    c3, c2, c23 = copies(g)
    d = Derivation(name, g.letters() + gl([c3, c2, c23]), out, L)
    # g c3 -> M (three wires): the merge over wire 3 is g . X3 g X3
    m1 = merge3_of(g)
    d.lemma(m1, 0)
    M = L[m1][1]
    # c2 c23 = X2 g X2 X2 X3 g X3 X2 ... put it as X2 (g c3) X2
    p = len(M)
    c2l, c23l = c2.letters(), c23.letters()
    # c2 = X2 core.. X2 ; c23 = X2 X3 .. X2 X3 ; want X2 [g][X3 g X3] X2
    q = p + len(c2l)                                     # start of c23
    d.win(q - 1, q + 1, []) if False else None
    # c2's last X2 and c23's first X2 cancel; c23's last letters X2 X3 -> X3 X2
    d.win(q - 1, q + 1, [])                              # X2 X2
    n = len(d.cur); d.comm(n - 2)                        # ... X3 X2
    d.lemma(m1, p + 1)                                   # X2 M X2
    d.win(0, len(d.cur), out)                            # three wires {t, 1, 2}
    d.done(); return name

def merge3_of(g):
    """g . X3 g X3 -> three-wire word, g = Gad(0, (), d, e)."""
    if g.letters() == R.letters(): return mergeR3()
    name = f'merge3 {g!r}'
    if name in L: return name
    c3 = Gad(g.t, (3,), g.d, g.e)
    d = Derivation(name, g.letters() + c3.letters(), [], L) if False else None
    # g X3 g X3 = d (core X3 core X3) d^-1 ... (core^e)
    dl = [(x, 0) for x in g.d]; idl = [(x, 0) for x in G.winv(list(g.d))]
    cl = G.core(0, g.e)
    lhs = g.letters() + c3.letters()
    tmp = Derivation(name + ' tmp', lhs, lhs, L)
    n = len(dl) + len(cl) + len(idl)
    for j in range(len(dl)): tmp.comm(n + j)              # X3 past d
    tmp.win(n - len(idl), n + len(dl), [])               # d^-1 d
    m = len(tmp.cur)
    for j in range(len(idl)): tmp.comm(m - 2 - j)        # last X3 past d^-1
    # d [cl X3 cl X3] d^-1
    if g.e == 1: tmp.lemma('merge3', len(dl))
    else:
        sp = G.sep_pass(Gad(0, (3,)), Gad(0), 3)
        tmp.lemma(G.inv_lemma(sp), len(dl)); tmp.lemma(G.inv_lemma('merge3'), len(dl))
    out = list(tmp.cur)
    d = Derivation(name, lhs, out, L)
    for st in tmp.steps: pass
    # redo the same steps on d
    for j in range(len(dl)): d.comm(n + j)
    d.win(n - len(idl), n + len(dl), [])
    m = len(d.cur)
    for j in range(len(idl)): d.comm(m - 2 - j)
    if g.e == 1: d.lemma('merge3', len(dl))
    else:
        d.lemma(G.inv_lemma(sp), len(dl)); d.lemma(G.inv_lemma('merge3'), len(dl))
    d.done(); return name

def caw_at(c, v, g):
    """Lambda_c(v) g Lambda_c(v)^-1 -> g with v on its target."""
    out = Gad(g.t, g.W, list(v) + list(g.d), g.e)
    name = f'CAw{c} {"".join(v)} {g!r}'
    if name in L: return name, out
    lw = [G.lam(c, g.t, x)[0] for x in v]; lwi = [G.lam(c, g.t, x)[0] for x in G.winv(list(v))]
    d = Derivation(name, lw + g.letters() + lwi, out.letters(), L)
    cur = g
    for i in range(len(v) - 1, -1, -1):
        nm, g2 = G.ca(c, v[i], cur); d.lemma(nm, i)
        p = i + len(g2.letters()); d.win(p, p + 2, []); cur = g2
    d.done(); return name, out

def conjF():
    """R0 F0 -> F0 Q."""
    name = 'conjF'
    if name in L: return name
    bd = BD(name, [R.letters(), F0], F0 + Qg.letters())
    bd.ins(0, F0)                                        # F0 F0^-1 R0 F0
    bd.split(1, [1, 1]); bd.split(4, [1, 1])             # F0 [SW] [CZ] R0 [CZ] [SW]
    bd.win(2, 1, [[CS01, CS01]]); bd.win(4, 1, [[CSd01, CSd01]])
    nm, g2 = caw_at(1, ['S', 'S'], R)
    bd.lem(2, 3, [g2.letters()], nm)                     # F0 SW g2 SW
    bd.join(1, 3)
    o = bd.off(1)
    bd.d.swapconj(o, len(g2.letters()), 0)
    g3 = Gad(1, (), g2.d, g2.e)
    bd.b = [F0, g3.letters()]; bd._check()
    sp = SP.spell(Gad(0, (), g2.d, g2.e), Ri)
    bd.lem(1, 1, [Qg.letters()], relabel(sp, PI01, L))
    return bd.done()

if __name__ == '__main__':
    print(merge_all(R, norm([('CX', 1, 0), CZ01])))
    print(conjF())

def merge_all_Q():
    """Qg . (copies) -> CZ01 CX01, from the merge of Ri at target 0 relabelled."""
    out0 = norm([CZ01, ('CX', 1, 0)])
    m = merge_all(Ri, out0)
    return relabel(m, PI01, L)

def sep_wire(A, B):
    for c in range(4):
        if c not in (A.t, B.t) and ((c in A.W) != (c in B.W)): return c
    raise ValueError(('not separated', A, B))

def pass_lemma(A, B):
    """A B -> B A for separated gadgets."""
    return G.sep_pass(A, B, sep_wire(A, B))

def P_krk():
    """R0 Q R0 rho kappa rho -> F0."""
    name = 'P krk'
    if name in L: return name
    rho, kap = copies(R), copies(Qg)
    blocks = [R, Qg, R] + rho + kap + rho
    bd = BD(name, [g.letters() for g in blocks], F0)
    gs = list(blocks)
    def mv_left(i, j):
        """move block i left to position j by passes."""
        while i > j:
            A, B = gs[i - 1], gs[i]                     # A B -> B A, i.e. B passes A backwards
            bd.swap(i - 1, pass_lemma(B, A), fwd=False)
            gs[i - 1], gs[i] = B, A; i -= 1
    for k in range(3): mv_left(3 + k, 1 + k)              # rho after the first R0
    for k in range(3): mv_left(6 + k, 5 + k)              # kappa past the second R0
    bd.join(0, 4); bd.join(1, 4); bd.join(2, 4)
    bd.lem(0, 1, [norm([('CX', 1, 0), CZ01])], merge_all(R, norm([('CX', 1, 0), CZ01])))
    bd.lem(1, 1, [L[merge_all_Q()][1]], merge_all_Q())
    bd.lem(2, 1, [norm([('CX', 1, 0), CZ01])], merge_all(R, norm([('CX', 1, 0), CZ01])))
    bd.win(0, 3, [F0])
    return bd.done()

def R0_P():
    """R0 . R0 Q R0 -> R0 Q R0 . Q."""
    name = 'R0 P -> P Q'
    if name in L: return name
    rho, kap = copies(R), copies(Qg)
    X = gl(rho + kap + rho)
    Xi = norm(inv(X))
    bd = BD(name, [R.letters(), R.letters(), Qg.letters(), R.letters()], gl([R, Qg, R, Qg]))
    bd.ins(4, X)
    bd.join(1, 4)
    bd.lem(1, 1, [F0], P_krk())
    bd.lem(0, 2, [F0, Qg.letters()], conjF())
    # Q passes Xi
    qx = P.pname([tuple(Qg.letters())], [tuple(X)])
    if qx not in L:
        d2 = BD(qx, [Qg.letters()] + [g.letters() for g in rho + kap + rho], X + Qg.letters())
        gs = rho + kap + rho
        for i, g in enumerate(gs):
            d2.swap(i, pass_lemma(Qg, g))
        d2.done()
    bd.swap(1, G.pass_inv_B([tuple(Qg.letters())], [tuple(X)]))
    bd.lem(0, 1, [gl([R, Qg, R]), X], P_krk(), fwd=False)
    bd.cancel(1)
    bd.split(0, [len(R.letters()), len(Qg.letters()), len(R.letters())])
    return bd.done()

def F10():
    """decoded braid: l_k l_{k+1} l_k = l_{k+1} l_k l_{k+1}."""
    name = 'F10'
    if name in L: return name
    hq = relabel(h_gad(), PI01, L); qdec = L[hq][0]
    bd = BD(name, [ROT, qdec, ROT], list(qdec) + ROT + list(qdec))
    bd.lem(0, 1, [R.letters()], rot_gad()); bd.lem(2, 1, [R.letters()], rot_gad())
    bd.lem(1, 1, [Qg.letters()], hq)
    bd.ins(0, Ri.letters())                              # Ri R R Q R
    bd.lem(1, 4, [R.letters(), Qg.letters(), R.letters(), Qg.letters()], R0_P())
    bd.cancel(0)
    bd.lem(0, 1, [qdec], hq, fwd=False); bd.lem(1, 1, [ROT], rot_gad(), fwd=False)
    bd.lem(2, 1, [qdec], hq, fwd=False)
    return bd.done()

if __name__ == '__main__':
    print(F10())

def all_facts():
    """the K-free consecutive facts at the canonical configurations."""
    return [F6(), F7a(), F7b(), F10()]

# ------------------------------------------------------------ bridges to the decoding's gadgets
SW01_, SW23_, CS12_ = ('SWAP', 0, 1), ('SWAP', 2, 3), ('CS', 1, 2)
GPP_MACRO = norm([('TOFF', 0, 1, 2), SW01_, SW23_, CS12_, SW23_, SW01_,
                  ('TOFF', 0, 1, 2), SW01_, SW23_, CS12_, CS12_, CS12_, SW23_, SW01_])

def bridge_gpp():
    """MultiControlled.G-pp 1 (unfolded to macro letters) -> the gadget's spelling."""
    name = 'bridge G-pp'
    if name in L: return name
    d = Derivation(name, GPP_MACRO, G.core(0, 1), L)
    d.swapconj(2, 1, 2); d.swapconj(1, 1, 0)            # Sw01 Sw23 CS12 Sw23 Sw01 -> CS03
    d.swapconj(4, 3, 2); d.swapconj(3, 3, 0)            # ... CS12^3 ... -> CS03^3
    d.win(3, 6, [('CSd', 0, 3)])
    d.done(); return name

def all_facts():
    """the K-free consecutive facts at the canonical configurations, and the bridges."""
    return [F6(), F7a(), F7b(), F10(), bridge_gpp()]
