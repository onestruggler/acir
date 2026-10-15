# The box calculus, continued: CNOTs and swaps of the controls.
#
# Canonical box BOX(0; 1,2,3,4), u = 0, (a,b) = (1,2), (c,e) = (3,4).
#   CXcb-box   CX(c->b) BOX CX(c->b) = BOX CCZ(a,c,e)
#   CXbc-box   CX(b->c) BOX CX(b->c) = BOX CCZ(a,b,e)
#   SWbc-box   SWAP(b,c) BOX SWAP(b,c) = BOX          (the corrections cancel)
#   nat-SWbc   SWAP(b,c) BOX SWAP(b,c) = BOX(u; a,c,b,e)  (relabelling)
#   sym-bc     BOX(u; a,b,c,e) = BOX(u; a,c,b,e)
# With the pairs exchanged (box-cP, box-tQ give BOX = (c1 P)^2 = (t Q)^2
# and the swaps inside a pair are definitional), these permute the
# controls arbitrarily.
import derivn, engine, box
from derivn import Derivation, show, norm1, unfold1
from engine import block_right, simplify
from f5 import pass_box_right

B0 = box.BOX


def push_swap(d, k, j, jp):
    """SWAP(j, jp) at k moves right to the end of the word, each letter it
    crosses relabelled (j <-> jp); boxes it cannot cross whole are
    unfolded.  The swap ends at the last position."""
    sw = d.cur[k]; pi = {j: jp, jp: j}
    while k + 1 < len(d.cur) and d.cur[k + 1] != sw:
        g = d.cur[k + 1]
        if not (derivn.support(g) & {j, jp}):
            d.comm(k); k += 1; continue
        if len(derivn.support(g) | {j, jp}) > derivn.N - 1:
            assert derivn.is_box(g), show([g])
            d.unfold(k + 1); continue
        d.win(k, 2, derivn.relabel_word([g], pi) + [sw]); k += 1
    return k


def build(L):
    # CX(c->b) BOX CX(c->b) = BOX CCZ(a,c,e)
    cx = ('CX', 3, 2)
    d = Derivation('CXcb-box', [cx, B0, cx], [B0, ('CCZ', 1, 3, 4)], L)
    i, m = pass_box_right(d, 0, 1, 'box-tQ')
    simplify(d, i, m + 1)
    d.done()

    cx = ('CX', 2, 3)
    d = Derivation('CXbc-box', [cx, B0, cx], [B0, ('CCZ', 1, 2, 4)], L)
    i, m = pass_box_right(d, 0, 1, 'box-tQ')
    simplify(d, i, m + 1)
    d.done()

    # SWAP(b,c) BOX SWAP(b,c) = BOX: the swap as three CNOTs, each pair
    # around the box a CCZ on the controls, and the CCZs cancel.
    sw = ('SWAP', 2, 3)
    d = Derivation('SWbc-box', [sw, B0, sw], [B0], L)
    a, b = ('CX', 2, 3), ('CX', 3, 2)
    d.win(0, 1, [a, b, a]); d.win(4, 1, [a, b, a])
    # a b a BOX a b a: the middle a BOX a first
    d.lemma('CXbc-box', 2)                  # a b BOX CCZ124 b a
    m = engine.block_left(d, 4, 1, 3)       # a b BOX b E a, E the conjugated CCZ
    d.lemma('CXcb-box', 1)                  # a BOX CCZ134 E a
    j = len(d.cur) - 1                      # the last a
    k, mm = block_right(d, 2, j - 2, j + 1) # a BOX a E'
    d.lemma('CXbc-box', 0)                  # BOX CCZ124 E'
    simplify(d, 1, len(d.cur) - 1)
    d.done()

    # SWAP(b,c) BOX SWAP(b,c) = BOX(u; a,c,b,e): naturality of the swap.
    B1 = ('BOX', 0, 1, 3, 2, 4)
    d = Derivation('nat-SWbc', [sw, B0, sw], [B1], L)
    d.comm(1) if False else None
    k = push_swap(d, 0, 2, 3)          # ... SWAP SWAP
    d.win(k, 2, [])
    engine.refold_boxes(d, 0, len(d.cur), [B1])
    d.done()

    d = Derivation('sym-bc', [B0], [B1], L)
    d.lemma('SWbc-box', 0, fwd=False)
    d.lemma('nat-SWbc', 0)
    d.done()
    return L


if __name__ == '__main__':
    L = box.build({})
    import f5
    f5.build(L)
    build(L)
    print(len(L), 'lemmas')
