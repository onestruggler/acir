#!/usr/bin/env python3
"""Find a small complete set of short relators at a fixed width.

Relators are found by meet-in-the-middle over the exact group: two
reduced words of length at most L/2 with the same value give the relator
w1 · reverse(w2) (every generator is an involution).  They are kept up
to rotation and reversal.  The structural rules of Circuit.Base
(involutions, disjoint commutations) are always included.  Then, from
the longest down, a relator is dropped when the rest still presents the
group (coset enumeration over the given subgroup reaches the expected
index), which leaves an irredundant set biased towards short relators.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import core as C


def reduced_words(ngens, length):
    """Words with no two equal neighbours, by length."""
    layer = [()]
    yield ()
    for _ in range(length):
        nxt = []
        for w in layer:
            for g in range(ngens):
                if not w or w[-1] != g:
                    nxt.append(w + (g,))
        yield from nxt
        layer = nxt


def canonical(r):
    """Least rotation of r or of its reverse; None if not cyclically reduced."""
    n = len(r)
    if n == 0 or r[0] == r[-1]:
        return None
    for i in range(n):
        if r[i] == r[(i + 1) % n]:
            return None
    forms = []
    for w in (r, tuple(reversed(r))):
        forms.extend(w[i:] + w[:i] for i in range(n))
    return min(forms)


def relators(rep: C.PermRep, half: int):
    ngens = len(rep.gens)
    buckets: dict[tuple, list] = {}
    for w in reduced_words(ngens, half):
        buckets.setdefault(rep.evaluate(w), []).append(w)
    found = set()
    for ws in buckets.values():
        for i, a in enumerate(ws):
            for b in ws[i + 1:]:
                r = a + tuple(reversed(b))
                # cancel at the junction
                while len(r) >= 2 and len(a) and len(b):
                    break
                c = canonical(free_reduce(r))
                if c:
                    found.add(c)
    return sorted(found, key=lambda r: (len(r), r))


def free_reduce(w):
    out = []
    for g in w:
        if out and out[-1] == g:
            out.pop()
        else:
            out.append(g)
    # cyclic reduction
    while len(out) >= 2 and out[0] == out[-1]:
        out = out[1:-1]
    return tuple(out)


def minimise(ngens, base, candidates, subgroup, target, limit):
    """Drop candidates, longest first, while the index stays at target."""
    keep = list(candidates)
    assert C.index(ngens, base + keep, subgroup, limit) == target, "not complete"
    for r in sorted(candidates, key=lambda r: (-len(r), r)):
        trial = [s for s in keep if s != r]
        if C.index(ngens, base + trial, subgroup, limit) == target:
            keep = trial
    return keep


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--width", type=int, default=2)
    ap.add_argument("--half", type=int, default=4, help="max length of each half word")
    ap.add_argument("--limit", type=int, default=200000)
    args = ap.parse_args()
    gs = C.GateSet(args.width)
    rep = C.PermRep(gs)
    base = C.structural(gs)
    cands = [r for r in relators(rep, args.half) if len(r) > 4 or r not in base]
    cands = [r for r in cands if canonical(r) not in {canonical(b) for b in base if len(b) > 2}]
    print(f"width {args.width}: {len(gs.names)} generators, {len(cands)} candidate relators")
    order = {1: 2, 2: 384}.get(args.width)
    keep = minimise(len(gs.names), base, cands, [], order, args.limit)
    for r in keep:
        print(f"  {len(r):2d}  {gs.show(r)}")
    print(f"{len(keep)} relators beyond the structural ones")


if __name__ == "__main__":
    main()
