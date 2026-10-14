#!/usr/bin/env python3
"""Natural rules for CCX+H on two wires (order 2304), and what they miss.

Derived letters: HH0 = H0 H1, CXr0 = HH0 CX0 HH0 (the CNOT from wire 0
to wire 1), Z i = H i X i H i.
"""
import sys, time
import core as C, coreH as H, staged as S


gs = H.GateSetH(2)
rep = H.PermRepH(gs)
a = S.Alphabet(gs, {"HH0": "H0 H1", "CXr0": "H0 H1 CX0 H1 H0",
                     "Z0": "H0 X0 H0", "Z1": "H1 X1 H1",
                     "SW0": "CX0 H0 H1 CX0 H1 H0 CX0",
                     "CZ0": "H1 H0 H1 CX0 H1 H0 H1"})

SEED = [
    "X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0",  # one wire: dihedral of order 16
    "X1 CX0 X1 = CX0 X0",            # X on the control propagates
    "CXr0 X0 CXr0 = X0 X1",
    "CX0 CXr0 CX0 CXr0 CX0 CXr0",    # S3 on two wires
    "H0 CX0 H0 = H1 CXr0 H1",        # CZ is symmetric
    "CX0 Z0 CX0 = Z0 Z1",            # Z on the target spreads to the control
    "Z1 CX0 = CX0 Z1",               # Z on the control commutes
    "SW0 H0 SW0 = H1",               # the swap moves H
    "CZ0 CXr0 CZ0 CXr0 = Z0",        # CZ and CNOT anticommute up to Z on the control
]

def complete(rels):
    return C.index_c(len(a.letters), rels + a.definitions(), (), 5_000_000) == 2304

def ddmin(cands, ok):
    keep = list(cands)
    assert ok(keep)
    chunk = max(1, len(keep) // 2)
    while True:
        ordered = sorted(keep, key=lambda r: (-len(r), r))
        for s in range(0, len(ordered), chunk):
            part = set(ordered[s:s + chunk])
            trial = [r for r in keep if r not in part]
            if trial != keep and ok(trial):
                keep = trial
        if chunk == 1:
            return keep
        chunk = max(1, chunk // 2)

if __name__ == "__main__":
    base = a.structural() + [r for t in SEED for r in S.rule(a, t)]
    assert S.sound(rep, a, base), "unsound seed"
    print("seed complete on two wires:", complete(base), flush=True)
    if not complete(base):
        cands = S.relators(rep, a, range(len(a.letters)), 5)
        print(len(cands), "candidates up to length 10", flush=True)
        extra = ddmin(cands, lambda rs: complete(base + rs))
        print(f"{len(extra)} extra relators:")
        for r in sorted(extra, key=lambda r: (len(r), r)):
            print(f"  {len(r):2d}  {a.show(r)}")
    seed_only = list(SEED)
    for t in reversed(SEED):
        trial = [s for s in seed_only if s != t]
        if complete(a.structural() + [r for x in trial for r in S.rule(a, x)]):
            seed_only = trial
            print("  redundant in the seed:", t, flush=True)


FINAL = [
    "X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0 X0 H0",  # needed on one wire
    "CXr0 X0 CXr0 = X0 X1",
    "SW0 H0 SW0 = H1",
    "CZ0 CXr0 CZ0 CXr0 = Z0",
]


def check_final():
    g1 = H.GateSetH(1)
    a1 = S.Alphabet(g1, {"Z0": "H0 X0 H0"})
    r1 = a1.structural() + [r for t in FINAL[:1] for r in S.rule(a1, t)]
    w1 = C.index_c(len(a1.letters), r1 + a1.definitions(), (), 100000)
    r2 = a.structural() + [r for t in FINAL for r in S.rule(a, t)]
    w2 = C.index_c(len(a.letters), r2 + a.definitions(), (), 5_000_000)
    return w1, w2
