#!/usr/bin/env python3
"""Does the kickback K_CCZ (at every placement) imply R4?  The finder
without R4, with K_CCZ and the short identities on three wires.

    python3 -B kick2.py [limit]
"""
import itertools
import sys
import time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import finder as F
import kick as K

limit = int(sys.argv[1]) if len(sys.argv) > 1 else 60_000
base = F.Alphabet(4, r4=False, placed=True)
extra = set()
for W in itertools.combinations(range(4), 3):
    extra |= base.short_identities(('T', W), 2)
for t, a, b, c in itertools.permutations(range(4)):
    extra.add(K.kick(base, 'CCZ', t, a, b, c))
A = F.Alphabet(4, r4=False, placed=True, extra=sorted(extra, key=lambda r: (len(r), r)))
print(len(A.rels), 'relators: no R4, K_CCZ a rule', flush=True)
R4 = 'CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 HH02 CX1>2 HH02'
w = A.word(R4)
t0 = time.time()
r = A.derive(w, limit, verbose=True)
print('R4', 'DERIVED' if r else 'not derived', round(time.time() - t0, 1), 's', flush=True)
