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
Functional Verification of Universal Quantum Circuits* (QPL 2018),
through section 4 — lemma 4.1 (isometry restrictions), lemma 4.2,
lemma 4.3 (Clifford progress & preservation) and corollary 4.4 for
circuits over {H, S, CZ}, stated about the circuit itself and ending in
a decision: whether such a circuit is the identity is decidable.  The
corollary's polynomial time bound is not formalised.  Its root is

```bash
agda +RTS -M10G -RTS PathSum/Theorems.agda
```

which covers the whole of `PathSum/`.  Run it under a heap cap as
shown: `Denotation` alone needs about 10 GB and five minutes, and the
rest of the directory well under a minute more.  The layers are the
multilinear dyadic polynomials (`Polynomial`, `Polynomial/Properties`),
the order of a phase polynomial and lemma 2.13 (`Order`), path-sums
(`Base`), the reduction rules of figure 2 (`Reduction`), the semantic
interface (`Semantics`), the completeness proof (`Clifford`), the ring
ℤ[ζ] and the denotation (`Cyclotomic`, `Denotation`), the test on a
fully reduced path-sum (`Identity`, `Decide`), and lemma 4.1 with the
circuit semantics (`Assign`, `AssignSum`, `Norm`, `Circuit`,
`CircuitAmp`, `CircuitSemantics`, `Isometry`).

The denotation is not an exponential sum over ℂ.  Every amplitude of a
Clifford+R_k path-sum is a ℤ-linear combination of powers of a
2^M-th root of unity, so `Cyclotomic` works in ℤ[ζ] = ℤ[X]/(X^H + 1)
and no analysis is needed: destructive interference is the single
relation ζ^H = -1.  `Denotation` builds the operator entries there and
proves the semantic interface — proposition 3.1 for all three rules,
lemma 4.2, and that equivalence of path-sums is an equivalence
relation — so `Theorems` states section 4.3 at that denotation rather
than at a hypothetical one.

Corollary 4.4 reduces not the circuit's path-sum but its isometry
restriction, and lemma 4.1 is what carries the verdict back.
`Circuit` gives both path-sums of a circuit over {H, S, CZ}: `⟦ C ⟧`
(definition 2.9) and its restriction `⟦ C ⟧ᴿ`, already reified.
`CircuitSemantics` proves proposition 2.10 for them — the entries of
`⟦ C ⟧` are the circuit's matrix, computed gate by gate — and that
every column has norm 1, the norm being the trace form of `Norm`.
`Isometry` proves lemma 4.1 for any path-sum whose columns have
trace-form norm at most 1; that definition 2.4 implies this is argued
in prose in its header, and circuits satisfy it by a theorem.  So
`Theorems` concludes about `⟦ C ⟧` itself: reduction of `⟦ C ⟧ᴿ`
either refutes the circuit or ends at a path-sum with no path
variables whose being the identity is exactly the circuit's, and
`Decide` settles that last question input by input.

The departures from the paper are recorded in the module headers.
Definition 2.1 ties the normalisation 1/√2^k to the number of path
variables, but the rules of figure 2 do not preserve that tie, so a
path-sum carries both indices; and with the normalisation explicit,
lemma 4.3 acquires a case the paper does not discuss, namely that the
rule the phase calls for may cost more normalisation than the
path-sum has.  That case is proved impossible for a path-sum that is
the identity, so lemma 4.3 holds as the paper states it.  The circuits
are over {H, S, CZ} rather than the paper's {H, CNOT, R_k}: they
generate the whole Clifford group, and every output is a single
variable, so the isometry restriction is reified by construction
where the paper uses Gaussian elimination.  Lemma 4.1 is proved under
`WellFormed`, a bound on column norms that definition 2.4 implies,
rather than under definition 2.4 itself, which would need adjoints
the denotation does not have.  Path-sums have no constant inputs.
