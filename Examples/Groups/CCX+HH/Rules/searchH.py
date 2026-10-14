#!/usr/bin/env python3
"""Small complete relator sets for CCX+H on one and two wires."""
import sys, time
import core as C, coreH as H
from search import reduced_words, canonical, free_reduce
import selftest as T

def group_order(rep):
    size, _ = T.schreier_relators(rep)
    return size

def relators(rep, ngens, half):
    buckets = {}
    for w in reduced_words(ngens, half):
        buckets.setdefault(rep.evaluate(w), []).append(w)
    found = set()
    for ws in buckets.values():
        for i, a in enumerate(ws):
            for b in ws[i + 1:]:
                c = canonical(free_reduce(a + tuple(reversed(b))))
                if c: found.add(c)
    return sorted(found, key=lambda r: (len(r), r))

def structural(gs):
    from itertools import combinations
    rels = [(g, g) for g in range(len(gs.names))]
    for a, b in combinations(range(len(gs.names)), 2):
        if not set(gs.wires[a]) & set(gs.wires[b]):
            rels.append((a, b, a, b))
    return rels

def minimise(ng, base, cands, order):
    keep = list(cands)
    idx = lambda rs: C.index_c(ng, base + rs, (), 5_000_000)
    assert idx(keep) == order, ("not complete", idx(keep))
    chunk = max(1, len(keep) // 2)
    while True:
        ordered = sorted(keep, key=lambda r: (-len(r), r))
        for s in range(0, len(ordered), chunk):
            part = set(ordered[s:s + chunk])
            trial = [r for r in keep if r not in part]
            if trial != keep and idx(trial) == order:
                keep = trial
        if chunk == 1: return keep
        chunk = max(1, chunk // 2)

if __name__ == "__main__":
    for n, half in ((1, 8), (2, 7)):
        gs = H.GateSetH(n); rep = H.PermRepH(gs)
        order = group_order(rep)
        t = time.time(); cands = relators(rep, len(gs.names), half)
        base = structural(gs)
        print(f"width {n}: order {order}, orbit {len(rep.points)}, {len(cands)} relators up to length {2*half} ({time.time()-t:.0f}s)", flush=True)
        keep = minimise(len(gs.names), base, cands, order)
        for r in sorted(keep, key=lambda r: (len(r), r)):
            print(f"  {len(r):2d}  {gs.show(r)}", flush=True)
