#!/usr/bin/env python3
"""Derive a four-wire classical identity from the tower's level-0
relators by a partial proof-producing coset enumeration over the
classical group on the wires 0, 1, 2.

Labels are elements of that group (S8, acting on both halves of wire
3), kept as canonical words: a rewriting of a label to its canonical
word is an identity of circuits on the wires 0 1 2, which NaturalP
derives on three wires (Kit.fast₃), so it is recorded as a "local"
relator.  Cosets along the target are defined first; the enumeration
stops at a limit, and the target is traced from coset 0: if it closes
there with the trivial label, the trace is a derivation.

    python3 -B partial4.py 'CCX0;12 CCX2;13 CCX0;12 CCX2;13 CCX0;13' [limit]
"""
import sys
import time
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import labelled as LB
import proofs as PR
import tower4 as T

DEFS = T.definitions()
LETTERS = list(range(len(T.LETTERS)))
# the letters whose circuits lie on the wires 0 1 2
LOW = [g for g in LETTERS if T.image_support((g,), DEFS) <= {0, 1, 2}]


def ev(word):
    p = tuple(range(T.D))
    for g in reversed(word):
        q = T.PERMS[g]
        p = tuple(q[x] for x in p)
    return p


def bfs(letters):
    best = {ev(()): ()}
    q = deque([()])
    while q:
        w = q.popleft()
        for x in letters:
            w2 = w + (x,)
            k = ev(w2)
            if k not in best:
                best[k] = w2
                q.append(w2)
    return best


CANLOW = None


def canlow():
    global CANLOW
    if CANLOW is None:
        CANLOW = bfs(LOW)
    return CANLOW


class PartialTC(LB.LabelledTC):
    """Labels in LOW, normalised; each normalisation lab ⟶ nf is a local
    relator lab · rev(nf) (an identity on the wires 0 1 2)."""

    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.local = {}          # relator word -> fact id deriving dec(lab) -> dec(nf)

    def join(self, left, right):
        lab = tuple(left) + tuple(right)
        nf = canlow()[ev(lab)]
        if nf == lab:
            return lab, []
        f = self._add(self.dec(lab), self.dec(nf), [(0, ('norm', (lab, nf)), True)])
        return nf, [(0, ('fact', f), True)]


def derive(target, limit=200_000):
    """(tc, steps) with steps rewriting target ⟶ ε, or None."""
    rels = T.relators_tower()
    axioms = [PR.Axiom(f'r{j}', r, ()) for j, r in enumerate(rels)]
    macros = {g: (g,) for g in LOW}
    seeds = [tuple(target[:i]) for i in range(1, len(target) + 1)]
    tc = PartialTC(len(LETTERS), axioms, macros, seed=seeds, limit=limit)
    try:
        live = tc.run()
        print('  enumeration closed:', len(live), 'live cosets', flush=True)
    except OverflowError:
        print('  stopped at', len(tc.rep), 'cosets', flush=True)
    i, f, lab, st = tc.walk(0, tuple(target))
    print(f'  trace: {i} of {len(target)} letters, ends at {tc.root(f)}, label {lab}', flush=True)
    if i == len(target) and tc.root(f) == 0 and lab == ():
        return tc, st
    return None


if __name__ == '__main__':
    target = tuple(T.INDEX_N[x] for x in sys.argv[1].split())
    assert ev(target) == tuple(range(T.D)), 'not an identity'
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 200_000
    t0 = time.time()
    res = derive(target, limit)
    print('derived' if res else 'not derived', round(time.time() - t0, 1), 's')
