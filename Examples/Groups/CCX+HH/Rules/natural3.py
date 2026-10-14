#!/usr/bin/env python3
"""A hand-written natural rule set on three wires, tested for completeness.

Derived gates: CXr i = HH i CX i HH i (the CNOT from wire i to i+1) and
SW i = CX i CXr i CX i (the swap of wires i, i+1).  Rules are stated on
the bottom wires and used at every placement.  If the set is not
complete, the minimiser finds the fewest extra relators (from all
relators of length at most 8 spanning three wires) that make it so.

Run under WSL: python3 -B natural3.py [candidates.pkl]
"""

import pickle
import sys

import staged as S
import stage3 as T
from minimise3 import minimise

from classical3 import CLASSICAL_RULES

# The one classical relation the natural rules above miss, in two forms
# (equivalent in S8; which one the other rules can use is tested).
TOFFOLI_CNOT = {
    "commutator": "CCX0 CXr0 CCX0 CXr0 = SW0 CCX0 SW0 CCX0",
    "order": "CCX0 CXr0 CCX0 CXr0 CCX0 CXr0 CCX0 CXr0 CCX0 CXr0 CCX0 CXr0",
}

HADAMARD_RULES = [
    "X0 HH0 X1 HH0 = HH0 X1 HH0 X0",   # X commutes with Z on the other wire
    "SW0 HH0 SW0 = HH0",               # HH is symmetric
    "HH0 HH1 = HH1 HH0",               # the two HH commute
    "SW0 HH1 SW0 = HH0 HH1",           # H1 H2 swapped is H0 H2
    "SW1 HH0 SW1 = HH0 HH1",           # H0 H1 swapped is H0 H2
    "CCX0 CXr0 HH0 CXr0 = CXr0 HH0 CXr0 CCX0",  # Toffoli and HH under a CNOT
]


def main():
    a = T.derived_setup()
    form = sys.argv[2] if len(sys.argv) > 2 else "commutator"
    texts = CLASSICAL_RULES + [TOFFOLI_CNOT[form]] + HADAMARD_RULES
    rules = a.structural() + [r for t in texts for r in S.rule(a, t)]
    assert S.sound(T.rep, a, rules), "a rule is not sound"
    print(f"natural rules ({form} form):", len(texts))
    got = T.checks(a, rules)
    print("checks (complete iff (5040, 17280)):", got, flush=True)
    if got == (5040, 17280) or len(sys.argv) < 2:
        return
    _, cands = pickle.load(open(sys.argv[1], "rb"))
    extra = minimise(rules, cands, sys.stdout)
    print(f"{len(extra)} extra relators needed:")
    for r in sorted(extra, key=lambda r: (len(r), r)):
        print(f"  {len(r):2d}  {a.show(r)}")


if __name__ == "__main__":
    main()
