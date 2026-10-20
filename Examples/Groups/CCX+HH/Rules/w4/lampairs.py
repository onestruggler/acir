#!/usr/bin/env python3
"""Controlled HH on four wires: which pairs commute, and the V_Z finder's
derivations of those commutations.

A controlled HH Λ(c, s; t, u) is HH on the wires t u under a control on
wire c of colour s (black: 1, white: 0), the gadget of NaturalP/Ctrl
(CHHa) placed with its borrowed wire the fourth one, and white controls
by X on c around it.  There are 6 · 2 · 2 = 24.  For every unordered
pair that commutes as matrices, try to derive the commutation; derived
ones are added as relators for the next (bootstrapping).

    python3 -B lampairs.py [limit]       writes lampairs.pkl
"""
import itertools
import pickle
import sys
import time
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent / 'wn'))
import g4vz as G
import g4dec as GDec
import gadgets as GD


def lam(A, c, s, t, u):
    b = next(x for x in range(4) if x not in (c, t, u))
    word = tuple(GDec.placed(A, k, i, {0: c, 1: t, 2: u, 3: b}) for k, i in GD.CHHa)
    if s == 0:
        x = A.INDEX[('X', c)]
        word = (x,) + word + (x,)
    return word


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 30_000
    extra = []
    V = G.VZFinder()
    A = V.A
    inst = []
    for t, u in itertools.combinations(range(4), 2):
        for c in range(4):
            if c in (t, u):
                continue
            for s in (0, 1):
                inst.append(((c, s, t, u), lam(A, c, s, t, u)))
    pairs = []
    for (k1, w1), (k2, w2) in itertools.combinations(inst, 2):
        r = w1 + w2 + w1 + w2
        if A.is_identity(r):
            pairs.append((k1, k2, r))
    print(len(inst), 'controlled HH;', len(pairs), 'commuting pairs', flush=True)
    derived = []
    for k1, k2, r in pairs:
        if derived:
            V = G.VZFinder(extra=[d[2] for d in derived])
        t0 = time.time()
        res = V.derive(r, limit)
        print(f'{k1} {k2}: {"derived" if res else "NOT derived"} {round(time.time() - t0, 1)} s', flush=True)
        if res:
            derived.append((k1, k2, r))
    pickle.dump(derived, open(HERE / 'lampairs.pkl', 'wb'))
    print(len(derived), 'of', len(pairs), 'derived')


if __name__ == '__main__':
    main()
