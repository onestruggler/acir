# (F5) on five wires: a CS of the bottom four wires is its two halves
# controlled by wire 4,  CS(x,y) = lambda0(CS) lambda1(CS),  lambda1(CS) the
# S-box of Lambda.agda (Five.Letters) and lambda0 = X4 lambda1 X4 —
# the three equations of Lambda/Split's record F5.
#
#   Xb-box   X_b BOX X_b = BOX CCZ(a,c,e)          (X on the box's second control)
#   F5-01, F5-12, F5-23
import derivn, engine, box
from derivn import Derivation, show, norm1, relabel_word
from engine import block_left, block_right

X = lambda w: ('X', w)


def box_pi(g):
    """the renaming of the canonical box onto g = BOX(u; a, b, c, e)."""
    u, a, b, c, e = g[1:]
    return {0: u, 1: a, 2: b, 3: c, 4: e}


def pass_box_right(d, i, m, form='box-cP'):
    """the block at i (m letters) passes the box right after it: the box in
    one of its four-letter forms, the block across, the form folded back.
    Returns the block's new start and length."""
    g = d.cur[i + m]
    pi = box_pi(g)
    d.lemma(form, i + m, pi=pi)
    i, m = block_right(d, i, m, i + m + 4)
    d.lemma(form, i - 4, fwd=False, pi=pi)
    return i - 3, m


def build(L):
    B0 = box.BOX
    # X_b BOX X_b = BOX CCZ(a, c, e), canonically X2 BOX(0;1,2,3,4) X2.
    d = Derivation('Xb-box', [X(2), B0, X(2)], [B0, ('CCZ', 1, 3, 4)], L)
    i, m = pass_box_right(d, 0, 1)
    engine.simplify(d, i, m + 1)
    d.done()

    def f5(name, cs, sig):
        u, x, (c1_, c2_), A = sig[1:]
        bx = ('BOX', u, x, c1_, c2_, A)
        d = Derivation(name, [X(4), sig, X(4), sig], [cs], L)
        d.unfold(3); d.unfold(1)
        # X4 bx C X4 bx C, C the four letters after each box
        mm = block_left(d, 6, 1, 2)
        print('  block', show(d.cur[2:2 + mm]))
        assert d.cur[2] == X(4), show(d.cur)
        # X4 bx X4 ... -> bx CCZ ...: X on the box's second control (wire 4)
        pi = box_pi(bx)
        assert pi[2] == 4
        d.lemma('Xb-box', 0, pi=pi)
        # bx M bx C: M the letters between the boxes
        j = d.cur.index(bx, 1)
        i, m = pass_box_right(d, 1, j - 1)
        # bx bx M' C
        d.lemma('box2', 0, pi=pi)
        engine.simplify(d, 0, len(d.cur))
        d.done()

    f5('F5-01', ('CS', 0, 1), ('SBOX', 2, 0, (4, 1), 3))
    f5('F5-12', ('CS', 1, 2), ('SBOX', 0, 1, (4, 2), 3))
    f5('F5-23', ('CS', 2, 3), ('SBOX', 0, 2, (4, 3), 1))
    return L


if __name__ == '__main__':
    L = box.build({})
    build(L)
    print(len(L), 'lemmas')
