# (F0) the borrowed-wire switch, Sigma(x; t,y | u,A) = Sigma(x; t,y | A,u).
#
# Canonical wires x, t, y, u, A = 0, 1, 2, 3, 4.  Sigma = beta_u R_A with
# beta_u = BOX(3; 0,1,2,4), R_A = T4 P T4 Pd, T4 = TOFF(4;1,2), P = CS(0,4);
# in the pairing (t,y), (x,A) the box is T3 C T3 C, T3 = TOFF(3;1,2), and
# beta_A = BOX(4; 1,2,0,3) is T4 C T4 C, with the same C = CCZ(0,3,4).
#
#   F0-B    CX(3->4) beta_u CX(3->4) = beta_u beta_A
#   F0-R    CX(3->4) R_A = R_A beta_A CX(3->4)
#   CXuA-S  CX(3->4) passes Sigma (F0-B, F0-R, box2)
#   CXAu-S  CX(4->3) passes Sigma (letter by letter)
#   SW-S    SWAP(3,4) passes Sigma (three CNOTs)
#   nat-S   SWAP(3,4) Sigma SWAP(3,4) = Sigma(x; t,y | A,u)  (relabelling)
#   F0      Sigma(x; t,y | u,A) = Sigma(x; t,y | A,u)
import derivn, engine, box, cross, boxbox
from derivn import Derivation, show, norm1
from boxsym import push_swap

S_uA = ('SBOX', 3, 0, (1, 2), 4)
S_Au = ('SBOX', 4, 0, (1, 2), 3)
CX, CXr, SW = ('CX', 3, 4), ('CX', 4, 3), ('SWAP', 3, 4)
T3, T4 = norm1(('TOFF', 3, 1, 2)), norm1(('TOFF', 4, 1, 2))
C = norm1(('CCZ', 0, 3, 4))
P, Pd = norm1(('CS', 0, 4)), norm1(('CSd', 0, 4))
CZ03, CS03, CSd03 = norm1(('CZ', 0, 3)), norm1(('CS', 0, 3)), norm1(('CSd', 0, 3))
CCZ012 = norm1(('CCZ', 0, 1, 2))
Bu = ('BOX', 3, 0, 1, 2, 4)        # the box of Sigma
BuP = ('BOX', 3, 1, 2, 0, 4)       # the same, paired (t,y), (x,A)
BA = ('BOX', 4, 1, 2, 0, 3)


def build(L):
    piu, piA = cross.box_pi(BuP), cross.box_pi(BA)

    # F0-R: CX R_A = R_A beta_A CX
    d = Derivation('F0-R', [CX, T4, P, T4, Pd], [T4, P, T4, Pd, BA, CX], L)
    d.win(0, 2, [T4, CX])
    d.win(1, 2, [P, CS03, C, CX])
    d.win(4, 2, [T4, CX])
    d.win(5, 2, [Pd, CSd03, C, CX])
    # T4 P CS03 C T4 Pd CSd03 C CX: CS03 meets CSd03
    d.win(2, 2, [C, CS03])
    d.comm(3)                                  # T4 P C T4 CS03 Pd CSd03 C CX
    d.win(4, 3, [Pd])                          # T4 P C T4 Pd C CX
    d.win(2, 0, [T4, T4])                      # T4 P T4 T4 C T4 Pd C CX
    d.win(6, 2, [C, Pd])                       # T4 P T4 T4 C T4 C Pd CX
    d.lemma('box-tQ', 3, fwd=False, pi=piA)    # T4 P T4 BA Pd CX
    k = boxbox.box_right(d, 3, 4)              # T4 P T4 Pd BA CX
    d.done()

    # F0-B: CX beta_u CX = beta_u beta_A
    d = Derivation('F0-B', [CX, BuP, CX], [BuP, BA], L)
    d.lemma('box-tQ', 1, pi=piu)               # CX T3 C T3 C CX
    d.win(0, 2, [T3, T4, CX])
    d.win(2, 2, [C, CZ03, CX])
    d.win(4, 2, [T3, T4, CX])
    d.win(6, 3, [C, CZ03])                     # T3 T4 C CZ03 T3 T4 C CZ03
    d.win(3, 2, [T3, CZ03, CCZ012])            # T3 T4 C T3 CZ03 CCZ012 T4 C CZ03
    d.win(5, 2, [T4, CCZ012])
    d.comm(4)                                  # T3 T4 C T3 T4 CZ03 CCZ012 C CZ03
    d.win(5, 2, [CCZ012, CZ03])
    d.win(6, 3, [C])                           # T3 T4 C T3 T4 CCZ012 C
    d.win(3, 2, [T4, T3])                      # T3 T4 C T4 T3 CCZ012 C
    d.win(4, 0, [C, C])                        # T3 T4 C T4 C C T3 CCZ012 C
    d.lemma('box-tQ', 1, fwd=False, pi=piA)    # T3 BA C T3 CCZ012 C
    boxbox.box_left(d, 1, 0)                   # BA, T3 conjugated, C T3 CCZ012 C
    boxbox.collect(d, 1, len(d.cur))
    d.lemma('box-tQ', 1, fwd=False, pi=piu)    # BA BuP
    boxbox.box_box(d, 0)
    d.done()

    # CXuA-S: CX(3->4) passes Sigma
    d = Derivation('CXuA-S', [CX, S_uA], [S_uA, CX], L)
    cross.deep_unfold(d, 1)                    # CX Bu T4 P T4 Pd
    boxbox.reorder(d, 1, BuP[2:])
    d.win(2, 0, [CX, CX])
    d.lemma('F0-B', 0)                         # BuP BA CX T4 P T4 Pd
    d.lemma('F0-R', 2)                         # BuP BA T4 P T4 Pd BA CX
    boxbox.box_left(d, 6, 2)                   # BuP BA BA T4 P T4 Pd CX
    d.lemma('box2', 1, pi=piA)
    boxbox.reorder(d, 0, Bu[2:])
    cross.deep_fold(d, 0, S_uA)
    d.done()

    # CXAu-S: CX(4->3) passes Sigma
    d = Derivation('CXAu-S', [CXr, S_uA], [S_uA, CXr], L)
    i, m = cross.pass_right(d, 0, 1, 2)
    if m > 1:
        m = engine.simplify(d, i, m)
    d.done()

    # SW-S
    d = Derivation('SW-S', [SW, S_uA], [S_uA, SW], L)
    d.win(0, 1, [CX, CXr, CX])
    d.lemma('CXuA-S', 2)
    d.lemma('CXAu-S', 1)
    d.lemma('CXuA-S', 0)
    d.win(1, 3, [SW])
    d.done()

    # nat-S
    d = Derivation('nat-S', [SW, S_uA, SW], [S_Au], L)
    cross.deep_unfold(d, 1)
    k = push_swap(d, 0, 3, 4)
    d.win(k, 2, [])
    engine.refold_boxes(d, 0, len(d.cur), [('BOX', 4, 0, 1, 2, 3)])
    cross.deep_fold(d, 0, S_Au)
    d.done()

    d = Derivation('F0', [S_uA], [S_Au], L)
    d.win(0, 0, [SW, SW])
    d.lemma('SW-S', 1)
    d.lemma('nat-S', 0)
    d.done()
    return L


def switch(d, k, fwd=True):
    """the S-box at k with its borrowed wires exchanged."""
    g = d.cur[k]
    u, x, (c1, c2), A = g[1], g[2], g[3], g[4]
    if fwd:
        pi = {3: u, 0: x, 1: c1, 2: c2, 4: A}
    else:
        pi = {3: A, 0: x, 1: c1, 2: c2, 4: u}
    d.lemma('F0', k, fwd=fwd, pi=pi)


if __name__ == '__main__':
    import boxsym, boxdash
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    build(L)
    print(len(L), 'lemmas')
