#!/usr/bin/env python3
"""Four wires, classical: index of the affine subgroup AGL(4,2) (X, CX,
CXr, SW) in the group the classical rules present.  Exactly
|A16| / |AGL(4,2)| = 32432400 means the classical rules present A16,
the affine fragment being complete at every width (NaturalP/Affine)."""
import check4 as K4
import staged as S
a, L = K4.a, K4.L
CL = [f"X{i}" for i in range(4)] + [f"{g}{i}" for g in ("CX", "CXr", "SW") for i in range(3)] + ["CCX0", "CCX1"]
AFF = [x for x in CL if not x.startswith("CCX")]
rels = a.structural([L[x] for x in CL]) + K4.all_rules() + a.definitions()
print("index of AGL(4,2) (32432400 iff complete):",
      S.restricted_index(a, rels, [L[x] for x in CL], [L[x] for x in AFF], limit=60_000_000), flush=True)
