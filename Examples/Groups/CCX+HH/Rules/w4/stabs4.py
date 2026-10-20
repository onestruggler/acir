#!/usr/bin/env python3
"""Can the finder derive what an equivariant decoder needs on four wires?

The canonical sign pair s = M_0 M_1 (negate the levels 0 and 1) is the
circuit X1 X2 X3 · HH03 · CCX3;12 · HH03 · X1 X2 X3 (a CCZ on wires
1 2 3 under negated controls).  Every placed letter that fixes the
levels 0 and 1 pointwise, and X0 (which exchanges them), commutes with s.
For each, try to derive the relator L s L s with the affine finder of
`g4partial.py` (with R4 among the relators unless --no-r4).

    python3 -B stabs4.py [limit] [--no-r4]
"""
import contextlib
import io
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import g4partial as G
import g4derive as GD
import tower4 as T

S = 'X1 X2 X3 HH03 CCX3;12 HH03 X1 X2 X3'


def main():
    r4 = '--no-r4' not in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    limit = int(args[0]) if args else 30_000
    s = G.word(S)
    m = GD.matrix(s)
    want = tuple((0, tuple((-1 if i in (0, 1) else 1) if j == i else 0 for j in range(T.D)))
                 for i in range(T.D))
    assert m == want, 'the sign pair circuit is wrong'
    rels = G.relators(r4)
    G.canaff()
    stab = [g for g in range(len(T.LETTERS)) if T.PERMS[g][0] == 0 and T.PERMS[g][1] == 1]
    stab.append(G.IX['X0'])
    ok = 0
    for g in stab:
        target = (g,) + s + (g,) + s
        assert GD.matrix(target) == GD.matrix(()), G.NAMES[g]
        t0 = time.time()
        with contextlib.redirect_stdout(io.StringIO()):
            res = G.derive(target, rels, limit)
        ok += res
        print(f'{G.NAMES[g]:8} {"derived" if res else "NOT derived"} {round(time.time() - t0, 1)} s', flush=True)
    print(ok, 'of', len(stab), 'derived')


if __name__ == '__main__':
    main()
