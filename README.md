# qupit — Agda formalisation

Agda formalisation of group presentations, normal forms, and complete
relation sets for multi-qudit Clifford circuits.

## Versions

| Component            | Version |
| -------------------- | ------- |
| Agda                 | 2.8     |
| Agda standard library| 2.4     |


The library configuration is in [`qupit.agda-lib`](qupit.agda-lib): it
includes the repository root (`.`) and depends on `standard-library`.

## Typechecking

`MainTheorems.agda` restates the headline theorems of this branch:

```bash
agda MainTheorems.agda
```

It states four results — that the symplectic normal form is unique,
and that each of the simplified symplectic rules, the V1 Clifford
rules and the paper's Figure 1 rules presents the group it is meant
to — and reaches, through them, everything those proofs rest on.

This is the `qupit` branch, so the root covers only that chain.  The
library's other developments are still in the tree but are not reached
from it: the symmetric, trivial and cyclic groups, the wreath product,
and the Clifford+T and U₃(ℤ[½,i]) amalgamations.  Check those on their
own roots if you touch them.
