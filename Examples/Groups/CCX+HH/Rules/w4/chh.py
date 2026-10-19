#!/usr/bin/env python3
"""Is HH on wires 0 1, controlled by wire 2 (either colour), a
three-wire CCX+HH circuit, i.e. in W(E8)?  W(E8) is the full
automorphism group of the lattice spanned by the orbit of 4 e_0 under
the three-wire gates, so membership is: the matrix maps that orbit to
itself."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import core as C

gs = C.GateSet(3)
rep = C.PermRep(gs)
pts = set(rep.points)

def chh(v, col):
    # HH on wires 0,1 where wire 2 == col
    out = list(v)
    for blk in range(2):
        if blk != col:
            continue
        base = blk << 2
        idx = [base | j for j in range(4)]
        w = [v[i] for i in idx]
        H = [[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]]
        for r in range(4):
            s = sum(H[r][c] * w[c] for c in range(4))
            if s % 2:
                return None
            out[idx[r]] = s // 2
    return tuple(out)

for col in (0, 1):
    ok = all(chh(v, col) is not None and chh(v, col) in pts for v in rep.points)
    print('controlled-HH, control colour', col, 'in W(E8):', ok, ' orbit size', len(pts))
