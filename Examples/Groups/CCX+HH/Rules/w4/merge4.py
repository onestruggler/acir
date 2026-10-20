#!/usr/bin/env python3
"""The merge of a white- and a black-controlled HH on four wires:
X3 · CHH · X3 · CHH = HH(0,1), CHH the controlled-HH gadget of
NaturalP/Ctrl (control 3, HH on 0 1, borrowing wire 2).  Tried with the
AGL finder and the V_Z finder (K_CCZ and coarse relators in both).

    python3 -B merge4.py [limit]
"""
import itertools
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
f = {0: 3, 1: 0, 2: 1, 3: 2}
chh = tuple(GDec.placed(A, k, i, f) for k, i in GD.CHHa)
x3 = A.IX['X3']
hh = A.IX['HH01']
target = (x3,) + chh + (x3,) + chh + (hh,)
assert A.is_identity(target), 'merge does not hold'
print(len(target), 'letters', flush=True)
t0 = time.time()
r = A.derive(target, limit, verbose=True)
print('AGL finder:', 'derived' if r else 'NOT derived', round(time.time() - t0, 1), 's', flush=True)
t0 = time.time()
r = V.derive(target, limit, verbose=True)
print('V_Z finder:', 'derived' if r else 'NOT derived', round(time.time() - t0, 1), 's', flush=True)
