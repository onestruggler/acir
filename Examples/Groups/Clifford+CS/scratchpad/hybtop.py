# The hybrid's facts at the top pair (n = 4: k_14 with the sink 13), at
# the transport that makes k_14 the canonical hybrid X0 HD X0:
#   (C-p), (C-l): k p = w k, k l = w' k for same-pair K-free words w, w'
#                 (the hybrid's units act on the gadget: ca);
#   (C-3):        k^3 = eps (Barenco's decomposition: HD = P1 X3 P3,
#                 three commuting factors, X3^3 = T CZ13 T = CZ13 CZ12);
#   (C-sc):       k commutes with p'_13 p'_13 p'_14 (the pair scalar).
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, inv, relabel, rename_letter, BY_NAME
import passes as P
from passes import L
import gadgetlib as G
from gadgetlib import Gad
import facts4 as F
import hyb_classes as HC
import hybsep2 as H
import samepair as SP
from t_lf import HD
from blocks import BD

def frame_top():
    """the transport taking k_14 to the canonical hybrid block."""
    Gp = F.group()
    k = F.decoded(14, 'k')
    for ops in Gp:
        b = F.TF(ops, [k])[0]
        if norm(list(b[1])) == norm(HD) and b[0] == (1, 0, 0, 0): return ops
    raise ValueError('no frame')

if __name__ == "__main__" and "frame" in sys.argv:
    ops = frame_top()
    print('frame', ops)
    for name, (a, kind) in [('k14', (14, 'k')), ('p14', (14, 'p')), ('q14', (14, "p'")), ('l14', (14, 'l')),
                            ('h14', (14, 'h')), ('p13', (13, 'p')), ('q13', (13, "p'")), ('l13', (13, 'l'))]:
        b = F.TF(ops, [F.decoded(a, kind)])[0]
        print(name, b[0], F.sem(b) if kind != 'k' else HC.hyb_roles(b[1]), show(list(b[1]))[:60])

from hybshift import xconj_gad, ins_x
from hybsym import pass_inv, bar_bar, bc_pass as _bc_unused
from hybfar import AX
from t_lf import SQRT_V, SQRT_VI

X0 = ('X', 0)
KB = norm(F.flatB(((1, 0, 0, 0), tuple(norm(HD)))))         # the hybrid k at the top frame
PPl = G.core(0, 1)
Rg = Gad(0, (), ['S', 'K'], -1)
Bq = H.Bar('SSKS', 1, 2, 0)

def hd_units():
    """HD -> its units: Barenco as a commutator of units, CK(3,0), and the inverses."""
    name = 'HD units'
    hd = norm(HD)
    nb = len(Bq.word())
    assert hd[:nb] == Bq.word() and hd[nb] == ('CK', 3, 0)
    Bi = hd[nb + 1:-2]; Ci = hd[-2:]
    cu = norm(H.comm_units(Bq)); cui = norm(inv(cu))
    units = cu + [('CK', 3, 0)] + cui + [('CKd', 3, 0)]
    if name in L: return name, units
    d = Derivation(name, hd, units, L)
    d.win(0, nb, cu)
    p = len(cu) + 1
    d.win(p, p + len(Bi), cui)
    p += len(cui)
    d.win(p, p + 2, [('CKd', 3, 0)])
    d.done(); return name, units

def hd_conj(g):
    """HD g -> g' HD (the hybrid's units act on the gadget g, target 0, controls black)."""
    hu, units = hd_units()
    hd = norm(HD)
    name = f'HD conj {g!r}'
    # compute g' by a scratch run
    s = Derivation(name + ' scratch', units + g.letters(), units + g.letters(), L)
    g2 = H.move_left(s, 0, units, g, True)
    if name in L: return name, g2
    d = Derivation(name, hd + g.letters(), g2.letters() + hd, L)
    d.lemma(hu, 0)
    g3 = H.move_left(d, 0, units, g, True)
    assert g3.letters() == g2.letters()
    d.lemma(hu, len(g2.letters()), forward=False)
    d.done(); return name, g2

def k_conj(g):
    """k g -> g' k, k = X0 HD X0 (g a gadget at target 0)."""
    n1, g1 = xconj_gad([0], g)                          # X0 g X0 -> g1
    n2, g2 = hd_conj(g1)                                # HD g1 -> g2 HD
    n3, g3 = xconj_gad([0], g2)                         # X0 g2 X0 -> g3
    name = f'k conj {g!r}'
    if name in L: return name, g3
    d = Derivation(name, KB + g.letters(), g3.letters() + KB, L)
    p = len(KB) + len(g.letters())
    ins_x(d, p, [0])                                    # X0 HD X0 g X0 X0
    d.lemma(n1, len(KB) - 1)                            # X0 HD g1 X0
    d.lemma(n2, 1)                                      # X0 g2 HD X0
    ins_x(d, 1 + len(g2.letters()), [0])                # X0 g2 X0 X0 HD X0
    d.lemma(n3, 0)                                      # g3 X0 HD X0
    d.done(); return name, g3

def h_block(): return norm([X0] + Rg.letters() + [X0])

def C_l():
    """k l -> p k."""
    name = 'top k l = p k'
    if name in L: return name
    nm, g3 = k_conj(Rg)
    s = SP.spell(g3, Gad(0))
    d = Derivation(name, KB + Rg.letters(), PPl + KB, L)
    d.lemma(nm, 0)
    if s: d.lemma(s, 0)
    d.done(); return name

def C_p():
    """k p -> p h k."""
    name = 'top k p = p h k'
    if name in L: return name
    nm, g3 = k_conj(Gad(0))
    nh, gh = xconj_gad([0], Rg)                         # h block -> gadget gh
    npr, g4 = SP.prod(Gad(0), gh)                       # p gh -> g4
    s = SP.spell(g3, g4)
    hb = h_block()
    d = Derivation(name, KB + PPl, PPl + hb + KB, L)
    d.lemma(nm, 0)
    if s: d.lemma(s, 0)
    d.lemma(npr, 0, forward=False)                      # p gh
    d.lemma(nh, len(PPl), forward=False)                # p X0 R X0
    d.done(); return name

if __name__ == '__main__' and 'pair' in sys.argv:
    for f in (C_l, C_p):
        n = f(); print('derived:', n, len(BY_NAME[n].steps), 'steps')

from hybsym import through_pieces

def Lq(x, a): return H.Bar(SQRT_V if a == 1 else SQRT_VI, 1, x, 0)
LFP = [Lq(2, -1), H.Tof(3, 1, 2), Lq(3, 1), H.Tof(3, 1, 2), Lq(3, -1)]

def bc_hd(Yq):
    """Y = L_13(V^a) passes HD = B C B^-1 C^-1, B = L_12(V^2), C = CK(3,0)."""
    Y = Yq.word(); Hw = norm(HD)
    name = P.pname([tuple(Y)], [tuple(Hw)])
    if name in L: return name
    Bw_ = Bq.word(); nb = len(Bw_)
    C = [('CK', 3, 0)]
    assert Hw[:nb] == Bw_ and Hw[nb] == C[0]
    Bi = Hw[nb + 1:-2]; Ci = Hw[-2:]
    iB = norm(inv(Bw_))
    Y1q = H.Bar(SQRT_VI if Yq.wv == SQRT_V else SQRT_V, 1, 3, 0); Y1 = Y1q.word()
    assert fp(norm(Ci + Y + C)) == fp(Y1)
    d = Derivation(name, Y + Hw, Hw + Y, L)
    d.lemma(bar_bar(Yq, Bq), 0)
    p = nb
    d.win(p, p + len(Y) + 1, C + Y1)
    p += 1
    d.win(p + len(Y1), p + len(Y1) + len(Bi), iB)
    d.lemma(pass_inv(bar_bar(Y1q, Bq), Y1, Bw_), p)
    d.win(p, p + len(iB), Bi)
    p += len(Bi)
    d.win(p, p + len(Y1) + len(Ci), Ci + Y)
    d.done(); return name

def C_3():
    """HD HD HD -> eps, and k^3 -> eps."""
    name = 'top HD^3'
    if name not in L:
        P1, Qw, P3 = Lq(2, -1).word(), Lq(3, 1).word(), Lq(3, -1).word()
        R1, S1 = Lq(2, 1).word(), Lq(3, 1).word()
        T = norm([('TOFF', 3, 1, 2)])
        X = T + Qw + T
        hd = norm(HD)
        assert L[AX][1] == P1 + X + P3
        # X = R1 HD S1
        xf = 'HD X form'
        if xf not in L:
            e = Derivation(xf, X, R1 + hd + S1, L)
            e.win(0, 0, R1 + P1); q = len(R1) + len(P1) + len(X); e.win(q, q, P3 + S1)
            e.lemma(AX, len(R1), forward=False); e.done()
        hp1 = through_pieces(Lq(2, -1), AX, LFP)                    # P1 HD -> HD P1
        hp3 = bc_hd(Lq(3, -1))                                      # P3 HD -> HD P3
        xp1 = 'X P1 -> P1 X'
        if xp1 not in L:
            bd = BD(xp1, [X, P1], P1 + X)
            bd.lem(0, 1, [R1, hd, S1], xf)
            bd.swap(2, bar_bar(Lq(3, 1), Lq(2, -1)))                # S1 P1 -> P1 S1
            bd.swap(1, hp1, fwd=False)                              # HD P1 -> P1 HD
            bd.win(0, 2, [P1, R1])
            bd.lem(1, 3, [X], xf, fwd=False)
            bd.done()
        xp3 = 'X P3 -> P3 X'
        if xp3 not in L:
            bd = BD(xp3, [X, P3], P3 + X)
            bd.lem(0, 1, [R1, hd, S1], xf)
            bd.win(2, 2, [P3, S1])
            bd.swap(1, hp3, fwd=False)
            bd.swap(0, bar_bar(Lq(2, 1), Lq(3, -1)))
            bd.lem(1, 3, [X], xf, fwd=False)
            bd.done()
        p31 = bar_bar(Lq(3, -1), Lq(2, -1))                         # P3 P1 -> P1 P3
        bd = BD(name, [hd, hd, hd], [])
        for i in range(3): bd.lem(i * 3, 1, [P1, X, P3], AX)
        b = ['P1', 'X', 'P3'] * 3
        def sw(i):
            a_, c_ = b[i], b[i + 1]
            if (a_, c_) == ('P3', 'P1'): bd.swap(i, p31)
            elif (a_, c_) == ('X', 'P1'): bd.swap(i, xp1)
            elif (a_, c_) == ('P3', 'X'): bd.swap(i, xp3, fwd=False)
            else: raise ValueError((a_, c_))
            b[i], b[i + 1] = b[i + 1], b[i]
        for i in (2, 1, 3, 5, 4, 3, 2, 6, 5): sw(i)
        assert b == ['P1'] * 3 + ['X'] * 3 + ['P3'] * 3, b
        bd.win(0, 3, [[('CZ', 1, 2)]])                              # P1^3 = L_12(V^-3) = CZ12
        x3 = 'X^3'
        if x3 not in L:
            e = Derivation(x3, X + X + X, [('CZ', 1, 3), ('CZ', 1, 2)], L)
            n = len(X)
            e.win(n - 1, n + 1, [])                                  # T T
            e.win(2 * n - 3, 2 * n - 1, [])
            e.win(1, 1 + 3 * len(Qw), [('CZ', 1, 3)])                # Q^3 = L_13(V^3) = CZ13
            e.win(0, 3, [('CZ', 1, 3), ('CZ', 1, 2)])                # T CZ13 T
            e.done()
        bd.lem(1, 3, [[('CZ', 1, 3), ('CZ', 1, 2)]], x3)
        bd.win(2, 3, [[('CZ', 1, 3)]])                              # P3^3 = CZ13
        bd.win(0, 3, [[]])
        bd.done()
    k3 = 'top k^3'
    if k3 not in L:
        d = Derivation(k3, KB + KB + KB, [], L)
        n = len(KB)
        d.win(n - 1, n + 1, []); d.win(2 * n - 3, 2 * n - 1, [])   # X0 X0 between
        d.lemma(name, 1)
        d.win(0, 2, [])
        d.done()
    return k3

if __name__ == '__main__' and 'cube' in sys.argv:
    n = C_3(); print('derived:', n, len(BY_NAME[n].steps), 'steps;', len(BY_NAME['top HD^3'].steps))

# ------------------------------------------------------------ (C-sc) the pair scalar
from lemmas5 import PP3
from hybsep3 import pass_spelled, gspellings
CCZ023, CCZ123, CSd23, CS23 = ('CCZ', 0, 2, 3), ('CCZ', 1, 2, 3), ('CSd', 2, 3), ('CS', 2, 3)
X1 = ('X', 1)
PP = norm(PP3)

def lem_IY():
    """Y = CCZ023 PP -> X1 PP X1 CCZ123 CSd23 (the PP white on 1 times a diagonal on the controls)."""
    name = 'IY'
    if name in L: return name
    pi = (0, 3, 2, 1)
    m1 = relabel('merge3', pi, L)                              # PP' X1 PP' X1 -> M1, PP' = form(0,1)
    lhs1 = L[m1][0]; M1 = L[m1][1]
    lemf, f01 = G.form_lemma(0, 1, 1)                          # PP -> form(0, 1)
    assert norm(f01) == lhs1[:len(f01)], (show(f01), show(lhs1))
    PPi = norm(inv(PP))
    Dw = [CCZ123, CSd23]
    rhs = [X1] + PP + [X1] + Dw
    d = Derivation(name, [CCZ023] + PP, rhs, L)
    P.insert_inverse(d, 0, PPi)                                # PPi PP CCZ PP
    n = len(PP)
    d.lemma(P.prove([tuple(PP)], [(CCZ023,)]), n)               # PPi CCZ PP PP
    d.lemma('PP2=E', n + 1)                                    # PPi CCZ023 CCZ123
    q = n
    d.win(q, q, [CS23, CSd23])                                 # PPi CS23 CSd23 CCZ023 CCZ123
    d.win(q + 1, q + 3, [CCZ023, CSd23])
    d.win(q + 2, q + 4, [CCZ123, CSd23])                       # PPi CS23 CCZ023 CCZ123 CSd23
    assert d.cur[q:q + 2] == norm(M1), (show(d.cur[q:q + 2]), show(M1))
    d.lemma(m1, q, forward=False)                              # PPi PP' X1 PP' X1 D
    d.lemma(lemf, q, forward=False)
    d.lemma(lemf, q + n + 1, forward=False)
    P.cancel_inverse(d, 0, PPi)
    d.done(); return name

def hd_passes_D():
    """HD passes the diagonal CCZ123 CSd23 on its controls, through [B, C]."""
    name = 'HD passes D'
    if name in L: return name
    hd = norm(HD); Dw = [CCZ123, CSd23]
    nb = len(Bq.word())
    Bi = hd[nb + 1:-2]; Ci = hd[-2:]
    from dec import inv1
    Bqi = H.Bar(inv1(list('SSKS')), 1, 2, 0)
    assert fp(norm(Bi)) == fp(Bqi.word())
    parts = [Bq.word(), [('CK', 3, 0)], Bqi.word(), [('CKd', 3, 0)]]
    objs = [Bq, (('CK', 3, 0),), Bqi, (('CKd', 3, 0),)]
    d = Derivation(name, hd + Dw, Dw + hd, L)
    d.win(nb + 1, nb + 1 + len(Bi), Bqi.word())
    q = nb + 1 + len(Bqi.word())
    d.win(q, q + 2, [('CKd', 3, 0)])
    # D moves left past the parts, last first
    pos = sum(len(x) for x in parts)
    for part, ob in reversed(list(zip(parts, objs))):
        pos -= len(part)
        for j, g in enumerate(Dw):
            Z = H.CCZp(3, 1, 2) if g[0] == 'CCZ' else (g,)
            if isinstance(ob, H.Bar) and g[0] == 'CCZ':
                Z = H.CCZp(1, 2, 3)
            d.lemma(pass_spelled(ob, Z), pos + j)
    d.win(len(Dw) + nb + 1, len(Dw) + nb + 1 + len(Bqi.word()), Bi)
    q = len(Dw) + nb + 1 + len(Bi)
    d.win(q, q + 1, Ci)
    d.done(); return name

def hd_passes_Y():
    name = 'HD passes Y'
    if name in L: return name
    hd = norm(HD); Y = [CCZ023] + PP
    from hybshift import hyb_pass_gad
    gw = Gad(0, (1,), (), 1)
    assert gw.letters() == [X1] + PP + [X1]
    d = Derivation(name, hd + Y, Y + hd, L)
    d.lemma(lem_IY(), len(hd))
    d.lemma(hyb_pass_gad(hd, gw, 1), 0)
    d.lemma(hd_passes_D(), len(gw.letters()))
    d.lemma(lem_IY(), 0, forward=False)
    d.done(); return name

def C_sc():
    """k z -> z k, z = q13 q13 q14 (the decoded pair scalar at the sink 13)."""
    name = 'top k z = z k'
    if name in L: return name
    ops = frame_top()
    q13 = norm(F.flatB(F.TF(ops, [F.decoded(13, "p'")])[0]))
    q14 = norm(F.flatB(F.TF(ops, [F.decoded(14, "p'")])[0]))
    z = q13 + q13 + q14
    Y = [CCZ023] + PP
    zf = 'top z form'
    if zf not in L:
        e = Derivation(zf, z, [X0] + Y + [X0], L)
        n = len(q13)
        e.win(n - 2, n + 2, [])                                # X1 X0 X0 X1
        pp1 = relabel('PP2=E', (1, 0, 2, 3), L)
        e.lemma(pp1, 2)                                         # X0 X1 CCZ023 X1 X0 q14
        e.comm(1); e.comm(2); e.win(3, 5, [])                   # X1 past CCZ023 and X0, cancel
        e.win(2, 4, [])                                         # X0 X0 (end of q13^2, start of q14)
        e.done()
    d = Derivation(name, KB + z, z + KB, L)
    n = len(KB)
    d.lemma(zf, n)                                              # KB X0 Y X0
    d.win(n - 1, n + 1, [])                                     # X0 HD Y X0
    d.lemma(hd_passes_Y(), 1)                                   # X0 Y HD X0
    d.win(1 + len(Y), 1 + len(Y), [X0, X0])
    d.lemma(zf, 0, forward=False)
    d.done(); return name

if __name__ == '__main__' and 'scalar' in sys.argv:
    n = C_sc(); print('derived:', n, len(BY_NAME[n].steps), 'steps')
