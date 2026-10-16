# The borrowed-wire switch on six wires, from five-wire windows (the
# joint paper's Lemma lamcalc (i) at n = 6, its b6.py).
#
#   b6-box   BOX(0; 1,2,3,4) = BOX(5; 1,2,3,4)    the dashed wire moves to
#            an idle wire: CX(0 -> 5) and CX(5 -> 0) each pass the box in
#            its form t Q t Q (t = TOFF(0;1,2), Q = CCZ(0,3,4)), hence so
#            does SWAP(0,5); and SWAP(0,5) renames the box letter by letter
#   b6-SA    Sigma(x; t,y | u, A) = Sigma(x; t,y | u, z)   the borrowed
#            wire A moves to an idle wire z: (F0) exchanges the roles of u
#            and A (a five-wire window here), b6-box moves the box's dashed
#            wire, and (F0) again
#   b6-Su    Sigma(x; t,y | u, A) = Sigma(x; t,y | z, A)   b6-box on the box
#
# Canonical wires: x, t, y, u, A, z = 0, 1, 2, 3, 4, 5 for the S-boxes.
import os
os.environ['DERIVN_N'] = '6'
import derivn
from derivn import Derivation, show, norm1

assert derivn.N == 6

B0 = ('BOX', 0, 1, 2, 3, 4)
B5 = ('BOX', 5, 1, 2, 3, 4)
t = norm1(('TOFF', 0, 1, 2))
t5 = norm1(('TOFF', 5, 1, 2))
Q = ('CCZ', 0, 3, 4)
Q5 = ('CCZ', 5, 3, 4)
c05 = ('CX', 0, 5)
c50 = ('CX', 5, 0)
SW = norm1(('SWAP', 0, 5))


def build(L):
    # CX(0 -> 5) B0 CX(0 -> 5) = B0
    d = Derivation('b6-cx05', [c05, B0, c05], [B0], L)
    d.win(1, 1, [t, Q, t, Q])
    d.win(0, 2, [t, t5, c05])
    d.win(2, 2, [Q, c05])
    d.win(3, 2, [t, t5, c05])
    d.win(5, 2, [Q, c05])
    d.win(6, 2, [])
    d.comm(1)                          # t5 Q -> Q t5
    d.win(2, 2, [t, t5])               # t5 t -> t t5
    d.win(3, 2, [])
    d.win(0, 4, [B0])
    d.done()
    # CX(5 -> 0) B0 CX(5 -> 0) = B0
    d = Derivation('b6-cx50', [c50, B0, c50], [B0], L)
    d.win(1, 1, [t, Q, t, Q])
    d.win(0, 2, [t, c50])
    d.win(1, 2, [Q, Q5, c50])
    d.win(3, 2, [t, c50])
    d.win(4, 2, [Q, Q5, c50])
    d.win(6, 2, [])
    d.comm(2)                          # Q5 t -> t Q5
    d.win(3, 2, [Q, Q5])
    d.win(4, 2, [])
    d.win(0, 4, [B0])
    d.done()
    # as commutations
    for c, nm in ((c05, 'b6-cx05'), (c50, 'b6-cx50')):
        d = Derivation(nm + '-c', [c, B0], [B0, c], L)
        d.win(2, 0, [c, c])
        d.lemma(nm, 0)
        d.done()
    # SWAP(0,5) passes B0
    d = Derivation('b6-sw', [SW, B0], [B0, SW], L)
    d.win(0, 1, [c05, c50, c05])
    d.lemma('b6-cx05-c', 2)
    d.lemma('b6-cx50-c', 1)
    d.lemma('b6-cx05-c', 0)
    d.win(1, 3, [SW])
    d.done()
    # SWAP(0,5) renames B0 to B5, letter by letter
    d = Derivation('b6-ren', [SW, B0, SW], [B5], L)
    d.unfold(1)
    letters = list(d.cur[1:-1])
    ren = {0: 5, 5: 0}
    for k, g in enumerate(letters):
        g2 = derivn.relabel_word([g], ren)[0]
        d.win(k, 2, [g2, SW])
    d.win(len(letters), 2, [])
    d.fold(0, B5)
    d.done()
    # the dashed wire moves
    d = Derivation('b6-box', [B0], [B5], L)
    d.win(0, 0, [SW, SW])
    d.lemma('b6-sw', 1)
    d.lemma('b6-ren', 0)
    d.done()

    # Sigma(x; t,y | u, A) = Sigma(x; t,y | z, A): the box's dashed wire
    S = ('SBOX', 3, 0, (1, 2), 4)
    Sz = ('SBOX', 5, 0, (1, 2), 4)
    d = Derivation('b6-Su', [S], [Sz], L)
    d.unfold(0)
    bx = d.cur[0]
    pi = {0: bx[1], 1: bx[2], 2: bx[3], 3: bx[4], 4: bx[5], 5: 5}
    d.lemma('b6-box', 0, pi=pi)
    # the inner one-control S-boxes are CS(x, A) whatever their dashed wire
    want = derivn.norm(derivn.unfold1(Sz))
    d.win(2, 1, [want[2]])
    d.win(4, 1, [want[4]])
    d.fold(0, Sz)
    d.done()
    # Sigma(x; t,y | u, A) = Sigma(x; t,y | u, z): F0, the dashed wire, F0
    SA = ('SBOX', 4, 0, (1, 2), 3)
    Sf = ('SBOX', 5, 0, (1, 2), 3)
    Sg = ('SBOX', 3, 0, (1, 2), 5)
    d = Derivation('b6-SA', [S], [Sg], L)
    d.win(0, 1, [SA])                  # (F0): a five-wire window
    d.lemma('b6-Su', 0, pi={0: 0, 1: 1, 2: 2, 3: 4, 4: 3, 5: 5})
    d.win(0, 1, [Sg])                  # (F0) again
    d.done()
    return L


if __name__ == '__main__':
    L = build({})
    for dd in derivn.DERIVATIONS:
        print(f'{dd.name}: {len(dd.steps)} steps')
