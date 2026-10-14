#!/usr/bin/env python3
"""The natural three-wire rule set: certification and irredundancy.

Run under WSL with ./tc built: python3 -B final3.py
"""
import time
import staged as S, stage3 as T, natural3 as N, classical3 as K

a = T.derived_setup()
TEXTS = K.CLASSICAL_RULES + [N.TOFFOLI_CNOT["commutator"]] + N.HADAMARD_RULES


def rules_of(texts):
    return a.structural() + [r for t in texts for r in S.rule(a, t)]


def complete(texts):
    return T.checks(a, rules_of(texts)) == (5040, 17280)


def certify_adjacent(texts):
    rels = rules_of(texts)
    k = T.certify_adjacent(a, rels)
    t = time.time()
    g = C_index(rels)
    return k, g, time.time() - t


def C_index(rels):
    import core as C
    K6 = [a.index[n] for n in T.ADJ]
    return C.index_c(len(a.letters), rels + a.definitions(), [(x,) for x in K6], 20_000_000)


def irredundant(texts):
    keep = list(texts)
    for t in reversed(texts):
        trial = [s for s in keep if s != t]
        if complete(trial):
            keep = trial
            print("  redundant:", t, flush=True)
    return keep


if __name__ == "__main__":
    assert complete(TEXTS)
    keep = irredundant(TEXTS)
    print(f"{len(keep)} of {len(TEXTS)} rules are needed:", flush=True)
    for t in keep:
        print("  ", t, flush=True)
    print("adjacent route (|P_K| = 128, index 5443200):", certify_adjacent(keep), flush=True)
