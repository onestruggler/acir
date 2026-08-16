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
`MainTheorems.agda`: a formalisation of M. Amy, *Towards Large-scale
Functional Verification of Universal Quantum Circuits* (QPL 2018), as
far as section 4.3 — lemma 4.3 (Clifford progress & preservation) and
corollary 4.4 — together with everything those rest on.  Its root is

```bash
agda PathSum/Theorems.agda
```

which covers the whole of `PathSum/`.  The layers are the multilinear
dyadic polynomials (`Polynomial`, `Polynomial/Properties`), the order
of a phase polynomial and lemma 2.13 (`Order`), path-sums (`Base`),
the reduction rules of figure 2 (`Reduction`), the semantic interface
(`Semantics`) and the completeness proof (`Clifford`).

The denotation is not an exponential sum over ℂ.  Every amplitude of a
Clifford+R_k path-sum is a ℤ-linear combination of powers of a
2^M-th root of unity, so `Cyclotomic` works in ℤ[ζ] = ℤ[X]/(X^H + 1)
and no analysis is needed: destructive interference is the single
relation ζ^H = -1.  `Denotation` builds the operator entries there and
proves the semantic interface — proposition 3.1 for all three rules,
lemma 4.2, and that equivalence of path-sums is an equivalence
relation — so `Theorems` states section 4.3 at that denotation rather
than at a hypothetical one.

Two departures from the paper are recorded in the module headers.
Definition 2.1 ties the normalisation 1/√2^k to the number of path
variables, but the rules of figure 2 do not preserve that tie, so a
path-sum carries both indices; and with the normalisation explicit,
lemma 4.3 acquires a case the paper does not discuss, namely that the
rule the phase calls for may cost more normalisation than the
path-sum has.  That case is returned as a labelled outcome, not
proved: it is an argument about magnitudes rather than rewriting.
