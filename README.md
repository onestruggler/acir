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

`MainTheorems.agda` restates the headline theorems and covers the whole
live library on its own:

```bash
agda MainTheorems.agda
```

It reaches the symmetric, Clifford+T and U₃(ℤ[½,i]) developments
through the results it states, so there is nothing left to check
separately.

## Path-sums

[`PathSum/`](PathSum/) is a separate development, not reached by
`MainTheorems.agda`: a formalisation of section 4.3 of M. Amy,
*Towards Large-scale Functional Verification of Universal Quantum
Circuits* (QPL 2018), namely lemma 4.3 (Clifford progress &
preservation) and corollary 4.4.  Its root is

```bash
agda PathSum/Clifford.agda
```

which covers the whole of `PathSum/`.  The layers are the multilinear
dyadic polynomials (`Polynomial`, `Polynomial/Properties`), the order
of a phase polynomial and lemma 2.13 (`Order`), path-sums (`Base`),
the reduction rules of figure 2 (`Reduction`), the semantic interface
(`Semantics`) and the completeness proof (`Clifford`).
