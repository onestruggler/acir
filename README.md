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
variables settles it by that test.  Around it are most of sections 2
and 3 — composition, the paper's gate set {H, CNOT, R_k}, unitarity,
the whole of figure 2 at any path variables — the paper's own route
through Gaussian elimination, equivalence of two circuits, and the
worked examples.  The polynomial time bounds are not formalised.  Its
root is

```bash
agda +RTS -M10G -RTS PathSum/Theorems.agda
```

which covers the whole of `PathSum/`.  Run it under a heap cap as
shown: `Denotation` alone needs about 10 GB and four to five minutes,
`Cyclotomic` about two minutes, and the rest of the directory several
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
proposition 2.10 for `⟦ C ⟧` and that every column of `⟦ C ⟧` has norm
1 in the trace form of `Norm`; of `⟦ C ⟧ᴿ` it proves that it has the
same diagonal and no off-diagonal paths.  `Isometry` proves lemma 4.1
for any path-sum whose columns have trace-form norm at most 1
(`WellFormed`).  So `Corollary` concludes about `⟦ C ⟧` itself:
reduction of `⟦ C ⟧ᴿ` either refutes the circuit or ends at a path-sum
with no path variables whose being the identity is exactly the
circuit's.  For such a path-sum, `Decide` characterises the identity
input by input, and `Syntactic` turns that, by Möbius inversion, into
the syntactic test the paper means: no normalisation, outputs the
inputs modulo 2, phase 0 modulo 2^M, coefficient by coefficient
(`corollary-4-4-any`, `corollary-4-4-syntactic`).

**Figure 2 in full.**  `Polynomial/Product`, `Polynomial/Substitution`,
`Polynomial/Boolean` and `Polynomial/Bind` add products, substitution,
Boolean-valued polynomials and lemma 2.5 for every Boolean polynomial
(with the lift proved unique).  `Reduction/General` has all four rules
at the head — [ω] and [HH] with Boolean-valued quotients, and [Case] —
proved sound in `Reduction/Sound`, `Reduction/CaseSound` and `Pairs`.
`Reorder` and `Anywhere` apply the linear rules at any internal path
variable, folding the renumbering into each rule; `Reorder/Pair` and
`Full` do the same for all four rules, [Case] at any pair.  Each
calculus is sound and strongly normalising; `Anywhere/Match` and
`Full/Match` decide whether a rule applies (reading the quotients off
the phase), so every path-sum reaches an irreducible one.
`Anywhere/Clifford` shows lemma 4.3 makes progress at *every* internal
variable, `Interference` proves lemma 4.2 for general quotients, and
`Full/Clifford` fills a gap in the proof of corollary 4.4: every rule
of figure 2 keeps a Clifford path-sum's phase of order at most 2, so
reducing `⟦ C ⟧ᴿ` by any rules in any order until none applies decides
the circuit.

**Composition.**  `Compose` defines sequential composition
(definition 2.6) and the tensor product; `Compose/Properties`,
`Compose/Laws` and `Compose/Matrix` prove proposition 2.7's operator
equation U_{ξ′∘ξ} = U_ξ′ U_ξ with no hypotheses, and the category laws
up to equivalence; `Compose/Gates`, `Compose/Clifford` and
`Compose/CRK` read definition 2.9 compositionally for both gate sets;
`Compose/Tensor` and `Compose/Swap` give remark 2.8's interchange law
and SWAP naturality.  `Compose/WellFormed` and `Compose/Counterexample`
show proposition 2.7's well-formedness claim false and prove what
survives: composing after an isometry preserves well-formedness.

**The ring, definition 2.4 and unitarity.**  `Ring` and `Ring/Laws`
make ℤ[ζ] a commutative ring with conjugation, `Hermitian` gives the
Hermitian form on columns, and `PartialIsometry` definition 2.4 on the
unnormalised operator, with an algebraic proof that a partial isometry
is `WellFormed` — so lemma 4.1 holds under the paper's own hypothesis;
`PartialIsometry/Strict` shows the converse fails.
`PartialIsometry/Unitary`, `Unitarity`, `Unitarity/Gates` and
`CRK/Unitarity` prove every circuit's path-sum unitary (U†U = UU† = I),
over both gate sets.  `GlobalPhase` extends lemma 4.1 and corollary 4.4
to a global phase ζ^e, which (SH)³ = ω·I needs.

**The paper's gate set.**  `Linear` has Z₂-linear forms, and
`CRK/Circuit` circuits over {H, CNOT, R_k, R_k†} whose wires carry
them: definition 2.9, and proposition 2.14.  `CRK/Amp` and
`CRK/Semantics` prove proposition 2.10 and unit columns.  Corollary 4.4
is reached two ways for the Clifford ones (every R_k with k ≤ 2):
`CRK/Compile` compiles them to {H, S, CZ}, and `Gauss`,
`Gauss/Forms` and `Gauss/Corollary` follow the paper, reifying the
restriction by Gaussian elimination — which either exhibits an input
whose diagonal entry vanishes or yields a restriction with only
internal path variables, to which lemma 4.3 applies.

**Size.**  `Size`, `Size/Sparse`, `Size/Monomials`, `Size/Submonomials`
and `Size/Terms` prove the size half of corollary 2.15: a circuit's
path-sum is represented exactly (`Size/Equivalence`) by a list of at
most (n + |C| + 1)^max(2,k) terms plus one linear form per output,
polynomial in n + |C| for fixed k — and, read literally in the volume
n·|C|, false for the empty circuit.  `Size/Interpreter` (with
`Interpreter/Clifford`, `Interpreter/Equivalence`) builds that
representation gate by gate, correctly, with every intermediate list
polynomially bounded.  That bounds the data, not a running time: no
machine model or complexity class is formalised.

**Equivalence and verification.**  `Adjoint` defines C†, `AmpLinear`
the linearity of the gate matrices, and `Miter` proves that C† undoes
C on both sides, so ⟦ C₁ ⟧ ≋ ⟦ C₂ ⟧ exactly when ⟦ C₁ ++ C₂ † ⟧ is the
identity; `Equivalence` decides equivalence of two Clifford circuits
over {H, S, CZ} by corollary 4.4 at the miter.  `Adjoint/Conjugate`,
`Adjoint/Gates` and `CRK/Conjugate` show C† is the adjoint proper, the
conjugate transpose.  `Miter/Compose`, `Compose/Apply` and
`CRK/Miter/Compose` state the miter as section 3 writes it, the
composite ⟦ C† ⟧ ∘ ξ against any specification ξ, with lemma 4.1 at
the miter.  `CRK/Adjoint`, `CRK/Miter` and `CRK/Equivalence` do the same
for {H, CNOT, R_k} and decide equivalence of its Clifford circuits by
Gaussian elimination.  `CRK/Validation` is section 5.1's translation
validation for circuits at any level: reducing the miter's restriction
by any rules to |x⟩ ↦ |x⟩ proves equivalence, and lemma 4.2's pattern
refutes it — sound at every level, complete for Clifford circuits.
`CRK/Specification` checks a circuit against a path-sum specification
through the composed miter, `Compose/Contraction` shows well-formedness
survives composition after any partial isometry, and
`Examples/Validation` runs the procedure on small Clifford+T miters.

**Examples.**  `Examples` and its submodules check the paper's worked
examples at precision M₀ = 0 — examples 2.2 and 2.12, section 3.1,
appendix B.1, examples 3.3 (Toffoli, with the seven-T circuit), 3.4
(controlled-T, with an ancilla) and B.2 (the adder) — each by the
paper's own derivation, every step's premises decided by computation
(`Polynomial/Decidable`, `Reduction/Decidable`,
`Reduction/General/Decidable`, `Reduction/Derivation`, `Congruence`,
`Ancilla`), with brute-force cross-checks (`Brute`).

The departures from the paper are recorded in the module headers.
Definition 2.1 ties the normalisation 1/√2^k to the number of path
variables, but the rules of figure 2 do not preserve that tie, so a
path-sum carries both indices; and with the normalisation explicit,
lemma 4.3 acquires a case the paper does not discuss, which is proved
impossible for a path-sum that is the identity.  Lemma 4.1 is proved
under `WellFormed`, which definition 2.4 implies and which is strictly
weaker.  Three statements are false as printed, and their corrected
forms are proved beside checked counterexamples: lemma 4.2 needs Q odd
at some input, not merely non-zero (Q = 2x₁); proposition 2.14's bound
is max(2, k), not k (a Hadamard's phase ½xy has order 2 whatever k
is); and proposition 2.7's well-formedness claim fails, for
`WellFormed` and for definition 2.4 alike.  Smaller slips: definition
2.6 omits a renaming in the outputs; section 4.1 substitutes Q where
x_i ⊕ Q is meant; example B.1 as printed is the identity, not ω·I; and
the fourth line of example 3.4 does not follow from the third.

Not formalised: the polynomial time bounds (proposition 3.2,
corollaries 2.15 and 4.4); constant inputs, beyond restricting to the
columns where an ancilla is |0⟩; the symmetric monoidal laws of remark
2.8 beyond interchange and SWAP naturality; and the benchmarks of
section 5.
