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
