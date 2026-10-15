# A controlled K between two controls of a box passes it up to a CCZ:
#
#   CKc-box    BOX CK(c->x) = C CK(c->x) C BOX,   C = CCZ(a, b, x)
#   CKdc-box   the same with CKd
#   CKc-boxL, CKdc-boxL    CK(c->x) BOX = BOX C CK(c->x) C
#
# (a, b the box's other controls.)  The box is X_c BOX X_c times C (Xb-box),
# the box negated on c, which CK(c->x) passes (it acts where c = 1, the
# negated box where c = 0); so BOX CK = (X_c BOX X_c) C CK, and C CK C
# passes the negated box too.  Canonical: BOX(0; 1,2,3,4), c, x = 3, 4.
import derivn, engine, cross, boxbox
from derivn import Derivation, show, norm1

B0 = ('BOX', 0, 1, 2, 3, 4)
B1 = ('BOX', 0, 1, 3, 2, 4)        # the order Xb-box wants, X on wire 3
X3 = ('X', 3)
C = norm1(('CCZ', 1, 2, 4))
PI_X = {0: 0, 1: 1, 2: 3, 3: 2, 4: 4}    # Xb-box's X(2) onto wire 3


def build(L):
    for G in ('CK', 'CKd'):
        g = (G, 3, 4)
        nm = f'{G}c-box'
        d = Derivation(nm, [B0, g], [C, g, C, B0], L)
        d.win(1, 0, [C, C])                        # B C C g
        boxbox.reorder(d, 0, B1[2:])
        d.lemma('Xb-box', 0, fwd=False, pi=PI_X)   # X3 B1 X3 C g
        d.win(3, 2, [C, g, C, C])                  # X3 B1 X3 C g C C
        i, m = cross.pass_left(d, 3, 3, 0)         # the block C g C before the negated box
        if d.cur[:m] != [C, g, C]:
            d.win(0, m, [C, g, C])
        d.lemma('Xb-box', 3, pi=PI_X)              # C g C B1 C C
        d.win(4, 2, [])
        boxbox.reorder(d, 3, B0[2:])
        d.done()

        d = Derivation(nm + 'L', [g, B0], [B0, C, g, C], L)
        d.lemma('box2', 0, fwd=False)              # B B g B
        d.lemma(nm, 1)                             # B C g C B B
        d.lemma('box2', 4)
        d.done()
    return L


def ckc(g, bx):
    """(lemma suffix, pi, order of bx's controls) when g is CK/CKd between
    two controls of bx."""
    if g[0] not in ('CK', 'CKd') or bx[0] != 'BOX' or len(bx) != 6:
        return None
    c, x = g[1], g[2]
    ctrls = bx[2:]
    if c not in ctrls or x not in ctrls:
        return None
    a, b = [y for y in ctrls if y not in (c, x)]
    return (f'{g[0]}c-box', {0: bx[1], 1: a, 2: b, 3: c, 4: x}, (a, b, c, x))


if __name__ == '__main__':
    import box, boxsym, boxdash, f5
    L = box.build({})
    f5.build(L)
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    build(L)
    print(len(L), 'lemmas')
