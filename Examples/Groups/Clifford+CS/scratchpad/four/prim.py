# Primitive four-wire derivations: the steps that the Agda chain engine
# (Four/Chain) accepts, each checked here as deriv.py checks the
# high-level ones.  A line is a list of macro letters (deriv.py gate
# tuples); every letter has the canonical Agda spelling of mac.py.
#
#   W  a literal window: the letters of the segment and of its
#      replacement are spelled off one wire m (their basic letters do
#      not touch m), and the two have the same operator: Windows.win at
#      the width-3 words with wire m deleted (one Same evaluation);
#   C  the structural commutation of a letter spelled within wires 0 1
#      and a letter spelled within wires 2 3 (TopWeakening.low-comm);
#   R  a re-bracketing: the segment and its replacement have the same
#      basic letters (by-assoc) — unfolding or folding a stacked letter;
#   A  one of the two four-wire rules at its canonical placement;
#   L  an earlier lemma, forward or backward.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mac import mac_tree, word_of, agda_of, supp_of, fp_basic, SWAP

def tree(g): return mac_tree(g)
def basic(word): return [b for g in word for b in word_of(tree(g))]
def spelled(g): return supp_of(word_of(tree(g)))
def fpw(word): return fp_basic(basic(word))

AX_CX = ([('CX', 3, 2), ('CCZ', 0, 1, 2), ('CX', 3, 2)], [('CCZ', 0, 1, 2), ('CCZ', 0, 1, 3)])
AX_TOFF = ([('TOFF', 0, 1, 2), ('CCZ', 0, 1, 3), ('TOFF', 0, 1, 2)], [('CCZ', 0, 1, 3), ('CCZ', 1, 2, 3)])
AX_CKT = ([('X', 0), ('CK', 0, 1), ('X', 0), ('TOFF', 1, 2, 3), ('CS', 0, 1), ('TOFF', 1, 2, 3)],
          [('TOFF', 1, 2, 3), ('CS', 0, 1), ('TOFF', 1, 2, 3), ('X', 0), ('CK', 0, 1), ('X', 0)])
AXIOMS = {'cx-ccz': AX_CX, 'toff-ccz': AX_TOFF, 'ck-tct': AX_CKT}

def split(g, h):
    """(i, bottom-first?) when g, h are spelled within the bottom i wires
    and the top 4 - i wires in some order, else None."""
    sg, sh = spelled(g), spelled(h)
    for i in (1, 2, 3):
        lo, hi = set(range(i)), set(range(i, 4))
        if sg <= lo and sh <= hi: return (i, True)
        if sh <= lo and sg <= hi: return (i, False)
    return None

def show(word): return ' '.join(g[0] + ''.join(str(w) for w in g[1:]) for g in word) if word else 'eps'

class Prim:
    """a primitive derivation from lhs; steps recorded for the emitter."""
    def __init__(self, name, lhs, rhs, lemmas):
        self.name, self.lhs, self.rhs = name, list(lhs), list(rhs)
        self.cur = list(lhs); self.steps = []; self.lemmas = lemmas
        assert fpw(self.lhs) == fpw(self.rhs), f'{name}: not semantically valid'

    def _set(self, k, n, ys, kind, info):
        seg = self.cur[k:k + n]
        assert fpw(seg) == fpw(ys), f'{self.name}: {kind} step changes the operator: {show(seg)} -> {show(ys)}'
        self.steps.append((kind, k, n, list(seg), list(ys), info))
        self.cur = self.cur[:k] + list(ys) + self.cur[k + n:]

    # a literal window missing wire m
    def W(self, k, n, ys, m):
        assert m is not None, f'{self.name}: window with no frame'
        seg = self.cur[k:k + n]
        for g in seg + list(ys):
            assert m not in spelled(g), f'{self.name}: {show([g])} is spelled on wire {m}'
        self._set(k, n, ys, 'W', m)

    # the structural commutation at k: a letter spelled within the bottom
    # i wires against one within the top 4 - i, in either order
    def C(self, k):
        g, h = self.cur[k], self.cur[k + 1]
        i = split(g, h)
        assert i is not None, f'{self.name}: C needs a split of the wires: {show([g, h])}'
        self._set(k, 2, [h, g], 'C', i)

    # a re-bracketing (the same basic letters)
    def R(self, k, n, ys):
        seg = self.cur[k:k + n]
        assert basic(seg) == basic(ys), f'{self.name}: R changes the letters: {show(seg)} -> {show(ys)}'
        self._set(k, n, ys, 'R', None)

    # a rule at its canonical placement
    def A(self, k, name, forward=True):
        l, r = AXIOMS[name]
        src, dst = (l, r) if forward else (r, l)
        assert self.cur[k:k + len(src)] == src, f'{self.name}: {name} does not match at {k}: {show(self.cur[k:k+len(src)])}'
        self._set(k, len(src), dst, 'A', (name, forward))

    def L(self, name, k, forward=True):
        l, r = self.lemmas[name]
        src, dst = (l, r) if forward else (r, l)
        assert self.cur[k:k + len(src)] == list(src), f'{self.name}: lemma {name} does not match at {k}: {show(self.cur[k:k+len(src)])}'
        self._set(k, len(src), list(dst), 'L', (name, forward))

    def done(self):
        assert self.cur == self.rhs, f'{self.name}: not finished: at {show(self.cur)}, want {show(self.rhs)}'
        self.lemmas[self.name] = (self.lhs, self.rhs)
        return self
