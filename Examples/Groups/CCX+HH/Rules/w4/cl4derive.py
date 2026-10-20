#!/usr/bin/env python3
"""Do the natural rules (with R4) derive the four-wire Clifford
relations?  A test with the affine finder of `g4partial.py`.

    python3 -B cl4derive.py [half] [limit]

Candidates: w1 · rev(w2) for words of at most `half` letters (default 3)
in the placed Clifford letters (X, CX, SW, HH) with the same action on
the 4320 minimal vectors of the Barnes–Wall lattice (a faithful action
of the Clifford group), spanning all four wires, freely reduced and not
a commutation of two letters on disjoint wires.  Each is traced by a
partial proof-producing enumeration over AGL(4, 2) (labels kept
canonical by affine completeness) with the rules and R4 as relators.
"""
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import g4partial as G
import cl4glue as CG

LETTERS = [g for g in range(len(G.NAMES)) if not G.NAMES[g].startswith('CCX')]


def cl4_perms():
    """The letters as permutations of the Clifford orbit of e0."""
    A = CG.Alph(4, False)
    names = {}
    for g in LETTERS:
        n = G.NAMES[g]
        names[g] = n          # same spelling: X i, CX c>t, SW ab, HH ab
    perms, npts = A.perm_rep([A.index[names[g]] for g in LETTERS])
    return {g: perms[A.index[names[g]]] for g in LETTERS}, npts


def main():
    half = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 30_000
    P, npts = cl4_perms()
    ident = tuple(range(npts))

    def ev(w):
        p = ident
        for g in reversed(w):
            q = P[g]
            p = tuple(q[x] for x in p)
        return p

    buckets = {}
    layer = [()]
    for _ in range(half):
        nxt = []
        for w in layer:
            for g in LETTERS:
                if not w or w[-1] != g:
                    nxt.append(w + (g,))
        for w in nxt:
            buckets.setdefault(ev(w), []).append(w)
        layer = nxt
    cands = set()
    for ws in buckets.values():
        ws.sort(key=len)
        for b in ws[1:]:
            r = ws[0] + tuple(reversed(b))
            if set().union(*(G.WIRES[g] for g in r)) != {0, 1, 2, 3}:
                continue
            if len(r) == 4 and r[0] == r[2] and r[1] == r[3] and not (G.WIRES[r[0]] & G.WIRES[r[1]]):
                continue
            if any(r[i] == r[i + 1] for i in range(len(r) - 1)):
                continue
            cands.add(r)
    # one representative per class under rotation, reversal and the
    # relabellings of the wires
    import itertools
    def relabel(g, pi):
        n = G.NAMES[g]
        import re
        digits = [int(c) for c in re.findall(r'\d', n)]
        base = n.rstrip('0123456789;>')
        if n.startswith('X'):
            return G.IX[f'X{pi[digits[0]]}']
        if n.startswith('CX'):
            return G.IX[f'CX{pi[digits[0]]}>{pi[digits[1]]}']
        a, b = sorted((pi[digits[0]], pi[digits[1]]))
        return G.IX[f'{n[:2]}{a}{b}']
    def key(r):
        best = None
        for pi in itertools.permutations(range(4)):
            w = [relabel(g, pi) for g in r]
            for rr in (w, w[::-1]):
                for i in range(len(rr)):
                    t = tuple(rr[i:] + rr[:i])
                    if best is None or t < best:
                        best = t
        return best
    classes = {}
    for r in cands:
        classes.setdefault(key(r), r)
    cands = sorted(classes.values(), key=lambda r: (len(r), r))
    print(len(cands), 'candidate four-wire Clifford relators, up to symmetry', flush=True)
    rels = G.relators(True)
    G.canaff()
    failed = []
    for k, r in enumerate(cands):
        t0 = time.time()
        import io, contextlib
        with contextlib.redirect_stdout(io.StringIO()):
            ok = G.derive(r, rels, limit)
        if not ok:
            failed.append(r)
            print('  NOT derived:', ' '.join(G.NAMES[g] for g in r), round(time.time() - t0, 1), 's', flush=True)
        if k % 20 == 0:
            print(f'  {k + 1}/{len(cands)} done, {len(failed)} not derived', flush=True)
    print(len(failed), 'of', len(cands), 'not derived')


if __name__ == '__main__':
    main()
