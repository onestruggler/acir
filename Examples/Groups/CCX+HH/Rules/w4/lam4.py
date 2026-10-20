#!/usr/bin/env python3
"""Short lemmas about controlled HH on four wires, by the V_Z finder.

Λ_c HH(0,1) is the controlled-HH gadget (NaturalP/Ctrl's CHHa) with its
control on wire c (black) and wire 2 or 3 borrowed.  The lemmas a pivot
decoder needs are statements about these:

    merge   X3 Λ3 X3 · Λ3 = HH01
    comm23  [Λ3 HH01, SW23 · Λ3 HH01 · SW23] = 1   (controls 3 and 2)

    python3 -B lam4.py [limit]
"""
import sys
import time
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent)); sys.path.insert(0, str(HERE)); sys.path.insert(0, str(HERE.parent / 'wn'))
import g4vz as G
import g4dec as GDec
import gadgets as GD

limit = int(sys.argv[1]) if len(sys.argv) > 1 else 30_000
V = G.VZFinder()
A = V.A
lam3 = tuple(GDec.placed(A, k, i, {0: 3, 1: 0, 2: 1, 3: 2}) for k, i in GD.CHHa)
sw23 = (A.IX['SW23'],)
lam2 = sw23 + lam3 + sw23
targets = {
    'comm23': lam3 + lam2 + lam3 + lam2,
}
for name, t in targets.items():
    assert A.is_identity(t), name
    t0 = time.time()
    r = V.derive(t, limit, verbose=True)
    print(name, len(t), 'letters:', 'derived' if r else 'NOT derived', round(time.time() - t0, 1), 's', flush=True)
