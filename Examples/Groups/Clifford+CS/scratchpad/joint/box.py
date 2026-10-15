# The box calculus on five wires, from four-wire windows: the core.
#
# The canonical box is BOX(0; 1, 2, 3, 4): dashed wire u = 0, controls
# a, b, c, e = 1, 2, 3, 4.  Its unfolding is
#     c1 t B t c1 B,   c1 = CCZ(u,a,b), t = TOFF(u;a,b), B = BOX(a; u,c,e),
# and B is CCZ(u,c,e) =: Q on four wires (a window).  With P = TOFF(u;c,e)
# (Q's X-form), W = c1 t and V = t c1 (the doubly controlled ZX and XZ on
# u), the facts, each a short chain of windows:
#
#   cQ      c1 Q = Q c1          two CCZs sharing u: c1 in two-wire pieces
#   tP      t P = P t            the same under K on u
#   VPQ     V (P Q) = (P Q) V    two doubly controlled XZs on u: under S on
#                                u each is a Toffoli times a CS on its
#                                controls (XZ = -i S X S^-1)
#   QVQ     Q V Q = P V P        from VPQ
#   box-tQ  BOX = t Q t Q
#   box-cP  BOX = c1 P c1 P      the X-form: QVQ, then tP
#   t-cP    t (c1 P c1 P) = (c1 P c1 P) t
#   box2    BOX BOX = eps        t inverts t Q t Q and fixes c1 P c1 P
#
# Every other box is a relabelling of the canonical one (a lemma used at a
# renaming of its wires).
import derivn, engine
from derivn import Derivation, show, norm1

U, A, B_, C, E = 0, 1, 2, 3, 4
BOX = ('BOX', U, A, B_, C, E)
c1 = ('CCZ', U, A, B_)
t = norm1(('TOFF', U, A, B_))
Q = ('CCZ', U, C, E)
P = norm1(('TOFF', U, C, E))
Bs = ('BOX', A, U, C, E)                   # the four-wire sub-box
CZab = ('CZ', A, B_)


def build(L):
    # c1 Q = Q c1: c1 in two-wire pieces (Barenco, the CNOT between a, b),
    # each passing Q in a window.
    d = Derivation('cQ', [c1, Q], [Q, c1], L)
    pieces = [('CS', B_, U), ('CX', A, B_), ('CSd', B_, U), ('CX', A, B_), ('CS', A, U)]
    d.win(0, 1, pieces)
    m = engine.move_left(d, len(pieces), 1, 0)
    d.win(m, len(pieces), [c1])
    d.done()

    # t P = P t: under K on u, t is c1 and P is Q.
    d = Derivation('tP', [t, P], [P, t], L)
    d.win(0, 1, [('K', U), c1, ('Kd', U)])
    d.win(3, 1, [('K', U), Q, ('Kd', U)])
    d.win(2, 2, [])                         # Kd K
    d.lemma('cQ', 1)
    d.win(2, 0, [('Kd', U), ('K', U)])
    d.win(0, 3, [P])
    d.win(1, 3, [t])
    d.done()

    # V (P Q) = (P Q) V, V = t c1: XZ = CSd S X S^-1 on the controlled block.
    V = [t, c1]
    d = Derivation('VPQ', V + [P, Q], [P, Q] + V, L)
    d.win(0, 2, [('CSd', A, B_), ('S', U), t, ('Sd', U)])
    d.win(4, 2, [('CSd', C, E), ('S', U), P, ('Sd', U)])
    # CSd34 left past Sd0, t, S0, CSd12 (disjoint or windows)
    engine.move_left(d, 4, 1, 0)
    # now CSd34 CSd12 S0 t Sd0 S0 P Sd0
    d.win(4, 2, [])                         # Sd0 S0
    d.lemma('tP', 3)
    d.win(4, 0, [('Sd', U), ('S', U)])      # CSd34 CSd12 S0 P Sd0 S0 t Sd0
    # CSd12 right past S0 P Sd0
    for k in (1, 2, 3):
        engine.ex(d, k)
    # CSd34 S0 P Sd0 CSd12 S0 t Sd0
    d.win(0, 4, [P, Q])
    d.win(2, 4, V)
    d.done()

    # Q V Q = P V P.
    d = Derivation('QVQ', [Q] + V + [Q], [P] + V + [P], L)
    d.win(0, 0, [P, P])                     # P P Q t c1 Q
    d.lemma('VPQ', 1, fwd=False)            # P t c1 P Q Q
    d.win(4, 2, [])
    d.done()

    # BOX = t Q t Q.
    d = Derivation('box-tQ', [BOX], [t, Q, t, Q], L)
    d.unfold(0)                             # c1 t Bs t c1 Bs
    d.win(2, 1, [Q]); d.win(5, 1, [Q])      # c1 t Q t c1 Q
    d.win(0, 2, [t, c1, CZab])              # t c1 CZab Q t c1 Q
    d.comm(2)                               # t c1 Q CZab t c1 Q
    d.lemma('cQ', 1)                        # t Q c1 CZab t c1 Q
    d.win(2, 4, [t])                        # t Q t Q
    d.done()

    # BOX = c1 P c1 P.
    d = Derivation('box-cP', [BOX], [c1, P, c1, P], L)
    d.unfold(0)
    d.win(2, 1, [Q]); d.win(5, 1, [Q])      # c1 t Q t c1 Q
    d.lemma('QVQ', 2)                       # c1 t P t c1 P
    d.lemma('tP', 1)                        # c1 P t t c1 P
    d.win(2, 2, [])
    d.done()

    # t (c1 P c1 P) = (c1 P c1 P) t.
    d = Derivation('t-cP', [t, c1, P, c1, P], [c1, P, c1, P, t], L)
    d.win(0, 2, [c1, t, CZab])              # c1 t CZab P c1 P
    d.comm(2)                               # c1 t P CZab c1 P
    d.lemma('tP', 1)                        # c1 P t CZab c1 P
    d.win(2, 3, [c1, t])                    # c1 P c1 t P
    d.lemma('tP', 3)
    d.done()

    # BOX BOX = eps.
    d = Derivation('box2', [BOX, BOX], [], L)
    d.lemma('box-tQ', 0)                    # t Q t Q BOX
    d.lemma('box-cP', 4)                    # t Q t Q c1 P c1 P
    d.win(4, 0, [t, t])                     # t Q t Q t t c1 P c1 P
    d.lemma('t-cP', 5)                      # t Q t Q t c1 P c1 P t
    d.lemma('box-cP', 5, fwd=False)         # t Q t Q t BOX t
    d.lemma('box-tQ', 5)                    # t Q t Q t t Q t Q t
    d.win(4, 2, [])                         # t Q t Q Q t Q t
    d.win(3, 2, [])
    d.win(2, 2, [])
    d.win(1, 2, [])
    d.win(0, 2, [])
    d.done()
    return L


if __name__ == '__main__':
    L = build({})
    print(len(L), 'lemmas')
