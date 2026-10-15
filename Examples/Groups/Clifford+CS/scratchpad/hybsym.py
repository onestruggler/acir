# The hybrid's control symmetry from Barenco's decomposition (LF):
# [Bar(V^2; 1,2 -> 0), CK(3 -> 0)] = [Bar(V^2; 1,3 -> 0), CK(2 -> 0)],
# exchanging the single control with a control of Barenco's pair.
#
# With P = L_12(V^-1), X3 = Toff(3;1,2) L_13(V) Toff(3;1,2), R = L_13(V^-1)
# LF reads HD = P X3 R, and at the relabelled hybrid H' = R X2 P with
# X2 = Toff(2;1,3) L_12(V) Toff(2;1,3).  Then
#   X3 = CX23 L_13(V) CX23            (the white half of the Toffoli passes)
#      = CX23 CX32 L_13(V) CX32 CX23  (CX32 passes L_13(V): its control 3)
#      = CX32 SWAP23 L_13(V) SWAP23 CX32 = CX32 L_12(V) CX32 = X2,
# and P, R pass X2 = L_13(V) H' L_12(V) (LF at H' rearranged): the
# doubly controlled V's commute group by group, and each passes H' -- R
# through H''s pieces, P (controlled by H''s single control 2) through
# H' = [B', C'] since C' = CK(2,0) carries L_12(V^-1) to L_12(V) on its
# own wires.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, inv, relabel, rename_letter, BY_NAME
import passes as P
from passes import L
import hybsep2 as H
import hybsep3 as H3
from hybsep import pass_groups
from hybfar import AX, lf_at
from t_lf import HD, LF, SQRT_V, SQRT_VI

def ren(word, pi): return norm([rename_letter(g, pi) for g in word])

PI = (0, 1, 3, 2)
HP = ren(HD, PI)                                  # [Bar(V^2; 1,3 -> 0), CK(2 -> 0)]
AXP = relabel(AX, PI, L)                          # HP -> LF(1, 3, 2, 0)

def Lw(x, a): return H.Bar(SQRT_V if a == 1 else SQRT_VI, 1, x, 0)
def word(q): return q.word()

def pass_(A, B):
    """lemma A B -> B A for two words, by the joint-spelling engine or groups."""
    return H3.pass_spelled(A, B)

def bar_bar(A, B):
    """two Barencos black on 1, same target 0: group by group."""
    Aw, Bw = A.word(), B.word()
    name = P.pname([tuple(Aw)], [tuple(Bw)])
    if name in L: return name
    if len(H.supp(Aw) | H.supp(Bw)) <= 3:
        return P.done_as(name, [tuple(Aw)], [tuple(Bw)], lambda d: d.win(0, len(Aw) + len(Bw), Bw + Aw))
    return pass_groups(name, H.groups_of(Aw), H.groups_of(Bw))

def x_to_y(z, w):
    """Toff(z;1,w) L_1z(V) Toff(z;1,w) -> CX(w,z) L_1z(V) CX(w,z)."""
    Q = Lw(z, 1); Qw = Q.word(); T = norm([('TOFF', z, 1, w)]); CX = [('CX', w, z)]
    lhs = T + Qw + T; rhs = CX + Qw + CX
    name = f'X->Y {z} {w}'
    if name in L: return name
    Wt = list(H.wtof(z, 1, w))
    d = Derivation(name, lhs, rhs, L)
    d.win(0, 1, CX + Wt)                              # Toff(z;1,w) = CX(w,z) Toff(z; not-1, w)
    d.win(1 + len(Wt) + len(Qw), 2 + len(Wt) + len(Qw), Wt + CX)
    d.lemma(H.wtof_pass(Q, z, w), 1, forward=False)              # Wt Q -> Q Wt
    p = 1 + len(Qw)
    d.win(p, p + 2 * len(Wt), [])
    d.done(); return name

def pass_inv(name0, Aw, Bw):
    """from A B -> B A (lemma name0), the lemma A inv(B) -> inv(B) A."""
    iB = norm(inv(Bw))
    name = f'{name0} ^inv'
    if name in L: return name
    d = Derivation(name, Aw + iB, iB + Aw, L)
    P.insert_inverse(d, 0, iB)                          # iB B A iB
    d.lemma(name0, len(iB), forward=False)              # iB A B iB
    P.cancel_inverse(d, len(iB) + len(Aw), Bw)
    d.done(); return name

CK20, CKd20 = norm([('CK', 2, 0)]), norm([('CKd', 2, 0)])
BQ = H.Bar('SSKS', 1, 3, 0)

def bc_pass(Yq):
    """Y = L_12(V^a) passes HP = B' C' B'^-1 C'^-1 (B' = L_13(V^2), C' = CK(2,0)):
    C' carries Y to L_12(V^-a) on its own wires."""
    Y = Yq.word(); Hw = HP
    name = P.pname([tuple(Y)], [tuple(Hw)])
    if name in L: return name
    Bw_ = BQ.word(); nb = len(Bw_)
    assert Hw[:nb] == Bw_ and Hw[nb] == CK20[0]
    Bi = Hw[nb + 1:-2]; Ci = Hw[-2:]
    assert fp(norm(Bw_ + Bi)) == fp([]) and fp(norm(CK20 + Ci)) == fp([])
    iB = norm(inv(Bw_))
    Y1q = H.Bar(SQRT_VI if Yq.wv == SQRT_V else SQRT_V, 1, 2, 0); Y1 = Y1q.word()
    assert fp(norm(Ci + Y + CK20)) == fp(Y1)
    d = Derivation(name, Y + Hw, Hw + Y, L)
    d.lemma(bar_bar(Yq, BQ), 0)                         # B' Y C' ...
    p = nb
    d.win(p, p + len(Y) + 1, CK20 + Y1)                 # Y C' -> C' Y1
    p += 1
    d.win(p + len(Y1), p + len(Y1) + len(Bi), iB)       # B'^-1 respelled
    d.lemma(pass_inv(bar_bar(Y1q, BQ), Y1, Bw_), p)     # Y1 B'^-1 -> B'^-1 Y1
    d.win(p, p + len(iB), Bi)
    p += len(Bi)
    d.win(p, p + len(Y1) + len(Ci), Ci + Y)             # Y1 C'^-1 -> C'^-1 Y
    d.done(); return name

def through_pieces(Yq, ax, pieces):
    """Y passes the hybrid ax's lhs, through its pieces (ax: hybrid -> pieces)."""
    Y = Yq.word(); Hw = L[ax][0]; Pw = L[ax][1]
    name = P.pname([tuple(Y)], [tuple(Hw)])
    if name in L: return name
    d = Derivation(name, Y + Hw, Hw + Y, L)
    d.lemma(ax, len(Y))
    p = 0
    for q in pieces:
        qw = q.word()
        if qw == Y: d.win(p, p + 2 * len(Y), Y + Y)
        elif isinstance(q, H.Bar): d.lemma(bar_bar(Yq, q), p)
        else: d.lemma(H3.pass_spelled(Yq, H3.TofG(q.z, q.c, q.w)), p)
        p += len(qw)
    d.lemma(ax, 0, forward=False)
    d.done(); return name

def xform():
    """X2 -> L_13(V) HP L_12(V), from LF at HP."""
    T2 = norm([('TOFF', 2, 1, 3)]); Q2 = Lw(2, 1).word()
    X2 = T2 + Q2 + T2
    R1, S1 = Lw(3, 1).word(), Lw(2, 1).word()
    P3, P1 = Lw(3, -1).word(), Lw(2, -1).word()
    name = 'X2 form'
    if name in L: return name
    assert L[AXP][1] == P3 + X2 + P1
    d = Derivation(name, X2, R1 + HP + S1, L)
    d.win(0, 0, R1 + P3)                                # R1 P3 = eps (a window on {0,1,3})
    q = len(R1) + len(P3) + len(X2)
    d.win(q, q, P1 + S1)
    d.lemma(AXP, len(R1), forward=False)
    d.done(); return name

def sym():
    name = 'hyb sym 23'
    if name in L: return name
    P1, P3 = Lw(2, -1).word(), Lw(3, -1).word()
    P2, Q2 = Lw(3, 1).word(), Lw(2, 1).word()
    R1, S1 = P2, Q2
    T3, T2 = norm([('TOFF', 3, 1, 2)]), norm([('TOFF', 2, 1, 3)])
    assert L[AX][1] == P1 + T3 + P2 + T3 + P3
    CX23, CX32, SW = ('CX', 2, 3), ('CX', 3, 2), ('SWAP', 2, 3)
    d = Derivation(name, HD, HP, L)
    d.lemma(AX, 0)                                      # P1 X3 P3
    p = len(P1)
    d.lemma(x_to_y(3, 2), p)                            # P1 CX23 P2 CX23 P3
    d.win(p + 1, p + 1, [CX32, CX32])
    d.lemma(H.spell_pass(Lw(3, 1), (CX32,)), p + 2, forward=False)   # CX32 P2 -> P2 CX32
    d.win(p, p + 2, [CX32, SW])                         # CX23 CX32 -> CX32 SWAP
    q = p + 2 + len(P2)
    d.win(q, q + 2, [SW, CX32])                         # CX32 CX23 -> SWAP CX32
    d.swapconj(p + 1, len(P2), 2)                       # SWAP P2 SWAP -> Q2
    d.lemma(x_to_y(2, 3), p, forward=False)             # P1 X2 P3
    d.lemma(xform(), p)                                 # P1 R1 HP S1 P3
    d.lemma(bar_bar(Lw(2, -1), Lw(3, 1)), 0)            # R1 P1 HP S1 P3
    d.lemma(bc_pass(Lw(2, -1)), len(R1))                # R1 HP P1 S1 P3
    q = len(R1) + len(HP)
    d.win(q, q + len(P1) + len(S1), S1 + P1)            # R1 HP S1 P1 P3
    q += len(S1)
    d.lemma(bar_bar(Lw(2, -1), Lw(3, -1)), q)           # ... S1 P3 P1
    q = len(R1) + len(HP)
    d.lemma(bar_bar(Lw(3, -1), Lw(2, 1)), q, forward=False)          # ... HP P3 S1 P1
    pieces = [Lw(3, -1), H.Tof(2, 1, 3), Lw(2, 1), H.Tof(2, 1, 3), Lw(2, -1)]
    d.lemma(through_pieces(Lw(3, -1), AXP, pieces), len(R1), forward=False)   # R1 P3 HP S1 P1
    d.win(0, len(R1) + len(P3), P3 + R1)                # P3 R1 HP S1 P1
    d.lemma(xform(), len(P3), forward=False)            # P3 X2 P1
    d.lemma(AXP, 0, forward=False)
    d.done(); return name

if __name__ == '__main__':
    n = sym()
    print('symmetry derived:', n, len(BY_NAME[n].steps), 'steps')
