#!/usr/bin/env python3
"""Three wires: do the Clifford-only natural rules present the even-H
Clifford group (order 2580480)?  Index of the two-wire subgroup."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import core as C, staged as S
from classical3 import CLASSICAL_RULES
from natural3 import TOFFOLI_CNOT, HADAMARD_RULES
import ss
import check4 as K4

gs = C.GateSet(3)
DER = {}
for i in range(2):
    DER[f"CXr{i}"] = f"HH{i} CX{i} HH{i}"
for i in range(2):
    DER[f"SW{i}"] = f"CX{i} HH{i} CX{i} HH{i} CX{i}"
a = S.Alphabet(gs, DER)
L = a.index
lets = [L[x] for x in [f"X{i}" for i in range(3)] + [f"{g}{i}" for g in ("CX", "CXr", "HH", "SW") for i in range(2)]]
sub = [g for g in lets if all(w < 2 for w in a.wires[g])]
texts = CLASSICAL_RULES + [TOFFOLI_CNOT["commutator"]] + HADAMARD_RULES
rels = a.structural(lets) + [r for t in texts for r in S.rule(a, t)] + a.definitions()
print("index (2240 iff complete):", S.restricted_index(a, rels, lets, sub, limit=20_000_000), flush=True)
