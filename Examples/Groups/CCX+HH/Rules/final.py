#!/usr/bin/env python3
"""Natural rules complete on one, two and three wires at once.

A rule only applies where it fits, so completeness is checked at each
width with the rules of that width: on two wires the group has order
384 (enumeration over 1), on three wires the S8 route of stage3.  The
irredundant subset keeps a rule only if dropping it breaks some width.

Run under WSL with ./tc built: python3 -B final.py
"""
import core as C
import staged as S
import stage3 as T
import natural3 as N
import classical3 as K

TEXTS = K.CLASSICAL_RULES + [N.TOFFOLI_CNOT["commutator"]] + N.HADAMARD_RULES

g2 = C.GateSet(2)
a2 = S.Alphabet(g2, {"CXr0": "HH0 CX0 HH0", "SW0": "CX0 HH0 CX0 HH0 CX0"})
a3 = T.derived_setup()


def fits(a, text):
    try:
        S.rule(a, text)
        return bool(S.rule(a, text))
    except KeyError:
        return False


def complete2(texts):
    rels = a2.structural() + [r for t in texts if fits(a2, t) for r in S.rule(a2, t)]
    return C.index_c(len(a2.letters), rels + a2.definitions(), (), 1_000_000) == 384


def complete3(texts):
    rels = a3.structural() + [r for t in texts for r in S.rule(a3, t)]
    return T.checks(a3, rels) == (5040, 17280)


def complete(texts):
    return complete2(texts) and complete3(texts)


if __name__ == "__main__":
    print("all 20: width 2", complete2(TEXTS), " width 3", complete3(TEXTS), flush=True)
    keep = list(TEXTS)
    for t in reversed(TEXTS):
        trial = [s for s in keep if s != t]
        if complete(trial):
            keep = trial
            print("  redundant:", t, flush=True)
    print(f"{len(keep)} rules, complete on two and three wires:", flush=True)
    for t in keep:
        print("  ", t, flush=True)
