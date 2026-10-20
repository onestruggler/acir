#!/usr/bin/env python3
"""The finder with coarse knowledge: short identities inside each P_w
(complete given R4), among the classical letters (complete on four
wires) and on each three wires (complete there), added as relators.
Tried on targets the plain finder misses.

    python3 -B coarse.py [length] [limit]
"""
import sys
import time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import finder as F

length = int(sys.argv[1]) if len(sys.argv) > 1 else 2
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 30_000
base = F.Alphabet(4, r4=True, placed=True)
extra = set()
t0 = time.time()
for kind in [('P', w) for w in range(4)] + [('C',)]:
    s = base.short_identities(kind, length)
    print(kind, len(s), 'short identities', flush=True)
    extra |= s
A = F.Alphabet(4, r4=True, placed=True, extra=sorted(extra, key=lambda r: (len(r), r)))
print(len(A.rels), 'relators', round(time.time() - t0, 1), 's', flush=True)
S = 'X1 X2 X3 HH03 CCX3;12 HH03 X1 X2 X3'
targets = {
    '[CX0>1, CZ23]': 'CX0>1 HH03 CX2>3 HH03 CX0>1 HH03 CX2>3 HH03',
    '[CCX0;12, s]': ('CCX0;12 ' + S + ' ') * 2,
    '[CCX1;02, s]': ('CCX1;02 ' + S + ' ') * 2,
}
for name, t in targets.items():
    w = A.word(t)
    assert A.is_identity(w), name
    t1 = time.time()
    r = A.derive(w, limit)
    print(name, 'derived' if r else 'NOT derived', round(time.time() - t1, 1), 's', flush=True)
