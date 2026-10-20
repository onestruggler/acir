#!/usr/bin/env python3
"""Is R4 derivable on four wires?  The finder without R4, with the rules
at every placement and the short identities on each three wires
(three-wire completeness, unconditional) as relators.

    python3 -B r4try.py [length] [limit]
"""
import itertools
import sys
import time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import finder as F

length = int(sys.argv[1]) if len(sys.argv) > 1 else 2
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 60_000
base = F.Alphabet(4, r4=False, placed=True)
extra = set()
for W in itertools.combinations(range(4), 3):
    extra |= base.short_identities(('T', W), length)
A = F.Alphabet(4, r4=False, placed=True, extra=sorted(extra, key=lambda r: (len(r), r)))
print(len(A.rels), 'relators (no R4)', flush=True)
R4 = 'CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 CCX0;12 HH03 HH02 CX1>2 HH02'
w = A.word(R4)
assert A.is_identity(w)
t0 = time.time()
r = A.derive(w, limit, verbose=True)
print('R4', 'DERIVED' if r else 'not derived', round(time.time() - t0, 1), 's', flush=True)
