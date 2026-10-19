#!/usr/bin/env python3
"""Four wires, classical: the second level of the chain.  P preserves
the partition by wire 3; its relators (those using only P's letters)
should give index 40320 = |P| / |S8| for the classical gates on wires
0 1 2, and those in turn should present S8 (index 5040 of <X0,X1,X2>)."""
import check4 as K4
import staged as S
a, L = K4.a, K4.L
P = ["X0", "X1", "X2", "X3", "CX0", "CX1", "CX2", "CXr0", "CXr1", "SW0", "SW1", "CCX0", "CCX1"]
S8 = ["X0", "X1", "X2", "CX0", "CX1", "CXr0", "CXr1", "SW0", "SW1", "CCX0"]
Xs = ["X0", "X1", "X2"]
rels = a.structural([L[x] for x in P]) + K4.all_rules() + a.definitions()
print("[P_R : S8] (40320):", S.restricted_index(a, rels, [L[x] for x in P], [L[x] for x in S8], limit=20_000_000), flush=True)
rels8 = a.structural([L[x] for x in S8]) + K4.all_rules() + a.definitions()
print("[S8_R : <X>] (5040):", S.restricted_index(a, rels8, [L[x] for x in S8], [L[x] for x in Xs], limit=20_000_000), flush=True)
