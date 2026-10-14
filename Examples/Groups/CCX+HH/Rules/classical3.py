#!/usr/bin/env python3
"""Natural classical rules on three wires: do they present S8?

The letters are X i, CX i, CXr i (CNOT from wire i to i+1), SW i (swap)
and CCX 0, all abstract: the check is coset enumeration of <X0, X1, X2>
in the group the rules present, which is 5040 exactly when they present
S8 (|S8| / 8).  Missing relators are found among the classical
relators of length at most 8 spanning three wires.

Run under WSL: python3 -B classical3.py candidates.pkl
"""
import pickle, sys
import staged as S, stage3 as T

CLASSICAL_RULES = [
    "SW0 = CX0 CXr0 CX0",              # a swap is three CNOTs
    "X1 CX0 X1 = CX0 X0",              # X on the control propagates
    "CXr0 X0 CXr0 = X0 X1",
    "CX0 CXr0 CX0 CXr0 CX0 CXr0",      # S3 on two wires
    "SW0 X0 SW0 = X1",                 # naturality of the swap
    "SW0 CX0 SW0 = CXr0",
    "SW0 SW1 SW0 = SW1 SW0 SW1",       # braid
    "SW0 SW1 CX0 SW1 SW0 = CX1",       # a two-wire gate moved up a wire
    "X0 CCX0 = CCX0 X0",
    "CX0 CCX0 = CCX0 CX0",
    "SW1 CCX0 SW1 = CCX0",
    "X1 CCX0 X1 = CCX0 SW1 CX0 SW1",
    "CX1 CCX0 CX1 = X1 CCX0 X1",
]

def main():
    a = T.derived_setup()
    S8 = [a.index[n] for n in T.CLASSICAL]
    Xs = [a.index[n] for n in ["X0", "X1", "X2"]]
    rules = a.structural(S8)
    for t in CLASSICAL_RULES:
        rs = S.rule(a, t)
        if not S.sound(T.rep, a, rs):
            print("UNSOUND:", t); return
        rules += rs
    p = S.restricted_index(a, rules, S8, Xs, limit=2_000_000)
    print("index of <X> (5040 iff S8):", p, flush=True)
    if p == 5040 or len(sys.argv) < 2:
        return
    _, cands = pickle.load(open(sys.argv[1], "rb"))
    cl = [r for r in cands if all(g in S8 for g in r)]
    print(len(cl), "classical candidates", flush=True)
    ok = lambda rs: S.restricted_index(a, rules + rs, S8, Xs, limit=2_000_000) == 5040
    keep = ddmin(cl, ok)
    print(f"{len(keep)} classical relators needed beyond the natural ones:", flush=True)
    for r in sorted(keep, key=lambda r: (len(r), r)):
        print(f"  {len(r):2d}  {a.show(r)}", flush=True)


def ddmin(cands, ok):
    """Drop chunks (longest relators first) while ok holds, down to single ones."""
    keep = list(cands)
    assert ok(keep), "the candidates do not complete the rules"
    chunk = max(1, len(keep) // 2)
    while True:
        ordered = sorted(keep, key=lambda r: (-len(r), r))
        for start in range(0, len(ordered), chunk):
            part = set(ordered[start:start + chunk])
            trial = [r for r in keep if r not in part]
            if trial != keep and ok(trial):
                keep = trial
        if chunk == 1:
            return keep
        chunk = max(1, chunk // 2)


if __name__ == "__main__":
    main()
