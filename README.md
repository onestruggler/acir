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
Functional Verification of Universal Quantum Circuits* (QPL 2018).  Its
core is section 4: lemma 4.1 (isometry restrictions), lemma 4.2, lemma
4.3 (Clifford progress & preservation), and the content of corollary
4.4's proof, about the circuit itself: a Clifford circuit is the
identity exactly when its restriction reduces to a path-sum that is
syntactically |x⟩ ↦ |x⟩, and any reduction that ends without path
variables settles it by that test.  Around it are the whole of figure 2
([Case] and Boolean-valued quotients included), the rules at any path
variable, lemma 2.5 in general, definition 2.4, the paper's gate set
{H, CNOT, R_k} with propositions 2.10 and 2.14, and equivalence of two
circuits through the miter.  The polynomial time bounds are not
formalised.  Its root is

```bash
agda +RTS -M10G -RTS PathSum/Theorems.agda
```

which covers the whole of `PathSum/`.  Run it under a heap cap as
shown: `Denotation` alone needs about 10 GB and four to five minutes,
`Cyclotomic` about two minutes, and the rest of the directory a few
minutes more.

**The core.**  The layers are the multilinear dyadic polynomials
(`Polynomial`, `Polynomial/Properties`) with Möbius inversion
(`Mobius`), the order of a phase polynomial and lemma 2.13 (`Order`),
path-sums (`Base`), the rules [Elim], [ω] and [HH] of figure 2 for
Z₂-linear quotients at the first path variable (`Reduction`), the
semantic interface (`Semantics`), the completeness proof (`Clifford`),
the ring ℤ[ζ] and the denotation (`Cyclotomic`, `Denotation`), the test
on a fully reduced path-sum (`Identity`, `Decide`, `Syntactic`), and
lemma 4.1 with the circuit semantics (`Assign`, `AssignSum`, `Norm`,
`Circuit`, `CircuitAmp`, `CircuitSemantics`, `Isometry`, `Corollary`).

The denotation is not an exponential sum over ℂ.  Every amplitude of a
Clifford+R_k path-sum is a ℤ-linear combination of powers of a
2^M-th root of unity, so `Cyclotomic` works in ℤ[ζ] = ℤ[X]/(X^H + 1)
and no analysis is needed: destructive interference is the single
relation ζ^H = -1.  `Denotation` builds the operator entries there and
proves the semantic interface — proposition 3.1 for the three linear
rules, lemma 4.2 for Z₂-linear quotients, the two undersized cases of
lemma 4.3, and that equivalence of path-sums is an equivalence
relation — so `Theorems` states section 4.3 at that denotation rather
than at a hypothetical one.

Corollary 4.4 reduces not the circuit's path-sum but its isometry
restriction, and lemma 4.1 is what carries the verdict back.
`Circuit` gives both path-sums of a circuit over {H, S, CZ}: `⟦ C ⟧`
(definition 2.9) and its restriction `⟦ C ⟧ᴿ`, already reified —
every output is a single variable.  `CircuitSemantics` proves
proposition 2.10 for `⟦ C ⟧` — its entries are the circuit's matrix,
computed gate by gate — and that every column of `⟦ C ⟧` has norm 1 in
the trace form of `Norm`; of `⟦ C ⟧ᴿ` it proves that it has the same
diagonal and no off-diagonal paths.  `Isometry` proves lemma 4.1 for
any path-sum whose columns have trace-form norm at most 1
(`WellFormed`).  So `Corollary` concludes about `⟦ C ⟧` itself:
reduction of `⟦ C ⟧ᴿ` either refutes the circuit or ends at a path-sum
with no path variables whose being the identity is exactly the
circuit's.  For such a path-sum, `Decide` characterises the identity
input by input, and `Syntactic` turns that, by Möbius inversion, into
the syntactic test the paper means: no normalisation, outputs the
inputs modulo 2, phase 0 modulo 2^M, coefficient by coefficient
(`corollary-4-4-any`, `corollary-4-4-syntactic`).  `Decide` also gives
a decision procedure along this route, though decidability by itself
is elementary — the matrix has finitely many entries.

**Figure 2 in full.**  `Polynomial/Product`, `Polynomial/Substitution`
and `Polynomial/Boolean` add the product of polynomials, substitution of
a polynomial for a variable, Boolean-valued polynomials, and lemma 2.5
for every Boolean polynomial, with the lift proved unique.
`Reduction/General` has all four rules at the head — [ω] and [HH] with
Boolean-valued quotients, and [Case] — and `Reduction/Sound`,
`Reduction/CaseSound` and `Pairs` prove them sound (appendix A).
`Reorder` and `Anywhere` apply the rules at any internal path variable,
folding the renumbering into each rule so that every step still removes
a variable: the length of a chain is exact, every path-sum is strongly
normalising, and `Anywhere/Match` decides whether a rule applies, so
every path-sum reaches an irreducible one.  `Anywhere/Clifford` shows
lemma 4.3 makes progress at *every* internal variable, not just some.
`Interference` proves lemma 4.2 for general quotients, and
`Anywhere/Corollary` and `Reduction/GeneralCorollary` carry the verdicts
of corollary 4.4 along these calculi.

**Definition 2.4 and unitarity.**  `Ring` gives ℤ[ζ] its product and
conjugation, `Hermitian` the Hermitian form on columns, and
`PartialIsometry` definition 2.4 on the unnormalised operator, together
with an algebraic proof that a partial isometry is `WellFormed`
(t² ≤ ‖G_xx‖² ≤ Σ ‖G_xx″‖² = 2^k·t for its Gram matrix) — so lemma 4.1
holds under the paper's own hypothesis.  `Unitarity` proves every
circuit over {H, S, CZ} an isometry, U†U = I.

**Equivalence.**  `Adjoint` defines C†, `AmpLinear` the linearity of
the gate matrices, and `Miter` proves that C† undoes C on both sides:
⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ exactly when ⟦ C₁ ++ C₂ † ⟧ is the identity, and a
path-sum is a circuit's exactly when C† maps its columns to basis
columns.  `Equivalence` decides equivalence of two Clifford circuits
by corollary 4.4 at the miter.

**The paper's gate set.**  `Linear` has Z₂-linear forms, and
`CRK/Circuit` circuits over {H, CNOT, R_k, R_k†} whose wires carry
them: definition 2.9, and proposition 2.14.  `CRK/Amp` and
`CRK/Semantics` prove proposition 2.10 and unit columns for them.
`CRK/Compile` compiles the Clifford ones (every R_k with k ≤ 2) to
{H, S, CZ}, giving corollary 4.4's characterisation for circuits with
CNOT; `CRK/Theorems` collects the package.

The departures from the paper are recorded in the module headers.
Definition 2.1 ties the normalisation 1/√2^k to the number of path
variables, but the rules of figure 2 do not preserve that tie, so a
path-sum carries both indices; and with the normalisation explicit,
lemma 4.3 acquires a case the paper does not discuss, namely that the
rule the phase calls for may cost more normalisation than the
path-sum has.  That case is proved impossible for a path-sum that is
the identity, so lemma 4.3 holds as the paper states it.  Lemma 4.1 is
proved under `WellFormed`, which definition 2.4 implies (a theorem) and
which is strictly weaker.  Two statements are false as printed, and
their corrected forms are proved beside checked counterexamples: lemma
4.2 needs Q odd at some input, not merely non-zero (Q = 2x₁), and
proposition 2.14's bound is max(2, k), not k (a Hadamard's phase ½xy
has order 2 whatever k is).

Not formalised: the polynomial time bounds (proposition 3.2,
corollaries 2.15 and 4.4); [Case] and Boolean-valued quotients at a
path variable other than the first; the Gaussian elimination by which
the paper's proof of corollary 4.4 reifies the restriction of a circuit
with CNOT (the characterisation is reached by compilation instead);
composition of path-sums (definition 2.6, proposition 2.7) and remark
2.8; constant inputs; equivalence of circuits with CNOT or R_k; and
UU† = I, so no path-sum is claimed unitary.
