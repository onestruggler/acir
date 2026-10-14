#!/usr/bin/env python3
"""Shrink a complete three-wire relator set while it stays complete.

Completeness is the pair of coset enumerations of `stage3.checks`
(index 5040 of <X> in the group the classical rules present, index 17280
of S8 in G_R).  Chunks of relators are dropped, longest first, halving
the chunk size each round (delta debugging), then a final pass tries
every relator alone.  Progress is logged, and the result saved, so the
run can be inspected or resumed.

Run under WSL: python3 -B minimise3.py candidates.pkl result.txt
"""

import pickle
import sys
import time

import stage3 as T

a = T.derived_setup()
GOAL = (5040, 17280)


def complete(base, rels):
    return T.checks(a, base + rels) == GOAL


def minimise(base, cands, log):
    keep = list(cands)
    assert complete(base, keep), "the starting set is not complete"
    chunk = max(1, len(keep) // 2)
    while True:
        ordered = sorted(keep, key=lambda r: (-len(r), r))
        for start in range(0, len(ordered), chunk):
            part = set(ordered[start:start + chunk])
            trial = [r for r in keep if r not in part]
            t = time.time()
            if trial != keep and complete(base, trial):
                keep = trial
                print(f"chunk {chunk}: dropped {len(part)}, {len(keep)} left "
                      f"({time.time() - t:.0f}s)", file=log, flush=True)
        if chunk == 1:
            break
        chunk = max(1, chunk // 2)
    return keep


def main():
    src, out = sys.argv[1], sys.argv[2]
    base, cands = pickle.load(open(src, "rb"))
    with open(out + ".log", "w") as log:
        keep = minimise(base, cands, log)
    with open(out, "w") as f:
        for r in sorted(keep, key=lambda r: (len(r), r)):
            f.write(f"{len(r):2d}  {a.show(r)}\n")
    pickle.dump(keep, open(out + ".pkl", "wb"))
    print(f"{len(keep)} relators beyond the two-wire and structural rules")


if __name__ == "__main__":
    main()
