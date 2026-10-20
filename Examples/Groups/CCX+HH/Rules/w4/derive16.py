#!/usr/bin/env python3
"""Derive the extra relators of the A16 tower (tower16extra.txt) from
level 0 and the affine extras, by partial proof-producing enumerations
over the affine group (labels canonical by affine completeness).

    python3 -B derive16.py [limit]

Pickles the derivations (derive16.pkl): per extra, its facts (the
closure of its trace) with steps naming relators ('r<j>' level 0,
'a<j>' affine extras), involutions, facts and affine norm steps."""
import sys
import time
import pickle
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import labelled as LB
import proofs as PR
import tower4 as T
import pipe16 as P16

AFF = [g for g in range(len(T.LETTERS)) if T.LETTERS[g][0] != 'CCX']


def ev(w):
    p = tuple(range(T.D))
    for g in reversed(w):
        q = T.PERMS[g]
        p = tuple(q[x] for x in p)
    return p


def canaff():
    best = {ev(()): ()}
    q = deque([()])
    while q:
        w = q.popleft()
        for x in AFF:
            w2 = w + (x,)
            k = ev(w2)
            if k not in best:
                best[k] = w2
                q.append(w2)
    return best


CAN = None


class PTC(LB.LabelledTC):
    def join(self, left, right):
        lab = tuple(left) + tuple(right)
        nf = CAN[ev(lab)]
        if nf == lab:
            return lab, []
        f = self._add(self.dec(lab), self.dec(nf), [(0, ('norm', (lab, nf)), True)])
        return nf, [(0, ('fact', f), True)]


def derive(target, rels, limit):
    axioms = [PR.Axiom(nm, r, ()) for nm, r in rels]
    macros = {g: (g,) for g in AFF}
    seeds = [tuple(target[:i]) for i in range(1, len(target) + 1)]
    tc = PTC(len(T.LETTERS), axioms, macros, seed=seeds, limit=limit)
    try:
        tc.run()
    except OverflowError:
        pass
    i, f, lab, st = tc.walk(0, tuple(target))
    if not (i == len(target) and tc.root(f) == 0 and lab == ()):
        return None
    top = tc._add(tuple(target), (), st)
    cl = sorted(P16.closure(tc, [top]))
    facts = {g: tc.facts[g] for g in cl}
    names = [a.name for a in tc.axioms]
    return top, facts, names


def main():
    global CAN
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
    rels = P16.named_relators([('a', HERE / 'aff4extra.txt')])
    extras = []
    for j, line in enumerate((HERE / 'tower16extra.txt').read_text().splitlines()):
        ws = line.split()
        if ws:
            extras.append((f'e{j}', int(ws[0]), tuple(T.INDEX_N[x] for x in ws[1:])))
    CAN = canaff()
    out = {}
    for nm, lvl, r in extras:
        t0 = time.time()
        res = derive(r, rels, limit)
        if res is None:
            print(f'{nm} (level {lvl}, length {len(r)}): NOT derived', round(time.time() - t0, 1), 's', flush=True)
            continue
        top, facts, names = res
        steps = sum(len(f.steps) for f in facts.values())
        print(f'{nm} (level {lvl}, length {len(r)}): {len(facts)} facts, {steps} steps',
              round(time.time() - t0, 1), 's', flush=True)
        out[nm] = (r, top, facts, names)
    pickle.dump(out, open(HERE / 'derive16.pkl', 'wb'))
    print(len(out), 'of', len(extras), 'derived')


if __name__ == '__main__':
    main()
