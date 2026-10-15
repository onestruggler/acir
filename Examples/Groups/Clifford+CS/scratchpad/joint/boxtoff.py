# A Toffoli with the dashed wire among its controls makes a second box:
#
#   Tu-box   TOFF(c; u, a) BOX_u TOFF(c; u, a) = BOX_u BOX_c
#
# Canonical wires u, a, b, c, e = 0, 1, 2, 3, 4: BOX_u = BOX(0; 1,2,3,4) is
# t Q t Q (t = TOFF(0;1,2), Q = CCZ(0,3,4)), and BOX_c = BOX(3; 1,2,0,4) is
# T' Q T' Q with the same Q (T' = TOFF(3;1,2)).  Conjugation by
# Tc = TOFF(3;0,1) sends t to t T' and Q to Q Q' (Q' = CCZ(0,1,4)); the Q'
# cancel, T' Q T' folds into BOX_c up to Q, and BOX_c passes t up to
# CCZ(1,2,4), which cancels with the one left by the Q'.
import derivn, engine, cross, boxbox
from derivn import Derivation, show, norm1

Bu = ('BOX', 0, 1, 2, 3, 4)
Bc = ('BOX', 3, 1, 2, 0, 4)
t, Tp, Tc = norm1(('TOFF', 0, 1, 2)), norm1(('TOFF', 3, 1, 2)), norm1(('TOFF', 3, 0, 1))
Q, Qp, Cabe = norm1(('CCZ', 0, 3, 4)), norm1(('CCZ', 0, 1, 4)), norm1(('CCZ', 1, 2, 4))


def build(L):
    pic = cross.box_pi(Bc)
    d = Derivation('Tu-box', [Tc, Bu, Tc], [Bu, Bc], L)
    d.lemma('box-tQ', 1)                       # Tc t Q t Q Tc
    d.win(0, 2, [t, Tp, Tc])
    d.win(2, 2, [Q, Qp, Tc])
    d.win(4, 2, [t, Tp, Tc])
    d.win(6, 3, [Q, Qp])                       # t T' Q Q' t T' Q Q'
    d.win(3, 2, [t, Qp, Cabe])                 # t T' Q t Q' Cabe T' Q Q'
    d.win(5, 2, [Tp, Cabe])                    # t T' Q t Q' T' Cabe Q Q'
    i, m = cross.pass_right(d, 4, 1, 6)        # t T' Q t T' Q' Cabe Q Q'
    assert m == 1 and d.cur[5] == Qp, show(d.cur)
    d.win(5, 2, [Cabe, Qp])
    d.win(6, 3, [Q])                           # t T' Q t T' Cabe Q
    i, m = cross.pass_right(d, 5, 1, 7)        # t T' Q t T' Q Cabe
    assert m == 1 and d.cur[6] == Cabe, show(d.cur)
    d.win(3, 2, [Tp, t])                       # t T' Q T' t Q Cabe
    d.win(4, 0, [Q, Q])                        # t T' Q T' Q Q t Q Cabe
    d.lemma('box-tQ', 1, fwd=False, pi=pic)    # t Bc Q t Q Cabe
    boxbox.box_left(d, 1, 0)                   # Bc, t up to CCZ(1,2,4), Q t Q Cabe
    boxbox.collect(d, 1, len(d.cur))
    d.lemma('box-tQ', 1, fwd=False)            # Bc Bu
    boxbox.box_box(d, 0)
    d.done()
    return L


if __name__ == '__main__':
    import box, boxsym, boxdash
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    build(L)
    print(len(L), 'lemmas')
