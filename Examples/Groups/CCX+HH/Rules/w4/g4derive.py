#!/usr/bin/env python3
"""Do the natural rules with R4 derive the short four-wire relations of
the CCX+HH group?  A test with the affine finder of `g4partial.py`.

    python3 -B g4derive.py [half] [limit] [--no-r4]

Candidates: w1 · rev(w2) for words of at most `half` letters (default 3)
in all 40 placed letters with the same 16 × 16 matrix (exact, columns
scaled by powers of 2), spanning all four wires, freely reduced, not a
commutation of letters on disjoint wires, one per class under rotation,
reversal and relabelling of the wires.  Each is traced by a partial
proof-producing enumeration over AGL(4, 2)."""
import sys
import re
import io
import time
import itertools
import contextlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE))
import g4partial as G
import tower4 as T

D = T.D


def act(g, col):
    """Apply letter g to a column (scale, entries)."""
    s, w = col
    n = G.NAMES[g]
    if n.startswith('HH'):
        a, b = int(n[2]), int(n[3])
        for t in (a, b):
            out = list(w)
            for x in range(D):
                if not x >> t & 1:
                    y = x | 1 << t
                    out[x], out[y] = w[x] + w[y], w[x] - w[y]
            w = out
            s += 1
        while s >= 2 and all(v % 2 == 0 for v in w):
            s -= 2
            w = [v // 2 for v in w]
        return s, tuple(w)
    p = T.PERMS[g]
    out = [0] * D
    for x in range(D):
        out[p[x]] = w[x]
    return s, tuple(out)


def matrix(word):
    cols = []
    for i in range(D):
        c = (0, tuple(1 if j == i else 0 for j in range(D)))
        for g in reversed(word):
            c = act(g, c)
        cols.append(c)
    return tuple(cols)


def relabel(g, pi):
    n = G.NAMES[g]
    d = [int(c) for c in re.findall(r'\d', n)]
    if n.startswith('X'):
        return G.IX[f'X{pi[d[0]]}']
    if n.startswith('CX'):
        return G.IX[f'CX{pi[d[0]]}>{pi[d[1]]}']
    if n.startswith('CCX'):
        a, b = sorted((pi[d[1]], pi[d[2]]))
        return G.IX[f'CCX{pi[d[0]]};{a}{b}']
    a, b = sorted((pi[d[0]], pi[d[1]]))
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


def main():
    r4 = '--no-r4' not in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    half = int(args[0]) if args else 3
    limit = int(args[1]) if len(args) > 1 else 30_000
    letters = list(range(len(G.NAMES)))
    ident = matrix(())
    buckets = {}
    layer = [()]
    for _ in range(half):
        nxt = []
        for w in layer:
            for g in letters:
                if not w or w[-1] != g:
                    nxt.append(w + (g,))
        for w in nxt:
            buckets.setdefault(matrix(w), []).append(w)
        layer = nxt
    cands = {}
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
            cands.setdefault(key(r), r)
    cands = sorted(cands.values(), key=lambda r: (len(r), r))
    print(len(cands), 'candidate four-wire relators up to symmetry', '(rules with R4)' if r4 else '(rules only)',
          flush=True)
    rels = G.relators(r4)
    G.canaff()
    failed = []
    for k, r in enumerate(cands):
        t0 = time.time()
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
