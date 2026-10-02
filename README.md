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
worked examples.  The polynomial time bounds are proved in an explicit
cost model (not a machine model) for fixed order and the linear rules,
corollary 4.4's for circuits over {H, S, CZ} and, by Gaussian
elimination, over the paper's gate set at level ≤ 2.  Its root is

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
and SWAP naturality up to equivalence.  `Permute`, `Permute/Sound`,
`Permute/Blocks` and `Compose/Monoidal` prove every symmetric monoidal
law — associativity, the unit laws, the braiding, the hexagon,
pentagon and triangle, interchange, SWAP naturality, and the category
laws of composition — as equality of path-sums up to renaming their
path variables (with the wires re-indexed where the two sides live on
n₁ + (n₂ + n₃) and (n₁ + n₂) + n₃ wires): "strictly equal", as far as
path-sums name their variables.  `CRK/Structural` proves the remark for
circuits: exchanging adjacent gates on disjoint wires changes the
path-sum only by a renaming of its path variables, which cannot be
dropped even modulo 2^M (`CRK/RenamingNeeded`); `Circuit/Trace` and
`Circuit/Structural` prove the same for circuits over {H, S, CZ}, for
⟦ C ⟧ and for its isometry restriction.  `Compose/Relabel` adds that
relabelling wires commutes with both compositions, that conjugation by
SWAP is relabelling, the drawn form of bifunctoriality and the second
hexagon; where definition 2.6's lifted outputs enter, these hold with
outputs modulo 2, and `Compose/Relabel/Sharp` shows nothing better
does.  `Compose/WellFormed` and `Compose/Counterexample`
show proposition 2.7's well-formedness claim false and prove what
survives: composing after an isometry preserves well-formedness.
`Signature`, `Signature/Compose`, `Signature/Clean` and
`Signature/WithX` add definition 2.1's constant inputs — a signature
makes each wire a variable or a Boolean constant, and the operator is
partial — with constants 0 exactly the library's |0⟩-restrictions;
section 2.1's compatibility condition, decided, in three forms (the
paper's syntactic one, along every path, and by the operator's
range); proposition 2.7 for signed path-sums under range
compatibility, which is exactly what it needs, beside the
post-selection counterexample (the identity, then |0⟩ ↦ |0⟩: the
composite erases, the product projects); footnote 1 as a reduction —
an ancilla is clean exactly when its preparation is compatible, so a
decider for compatibility decides unsatisfiability through footnote
2's circuits; and preparing |1⟩ as preparing |0⟩ and applying X.

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

**Polynomial time, in a cost model.**  `Cost` is a monad counting unit
steps (arithmetic below 2^M, Booleans, Fin comparisons, list and vector
cells), in which each algorithm is written once, so its count cannot
drift from it: a cost model, not a machine model.  `Cost/Monomial`,
`Cost/Coeff`, `Cost/Canon`, `Cost/Split`, `Cost/Subst` and
`Cost/Rules` keep phases of bounded order as canonical sparse lists and
run [Elim], [ω] and [HH] with linear quotients on them, each proved a
step of `Anywhere`'s calculus at polynomial cost; `Cost/Complete`,
`Cost/Search`, `Cost/Sequence` and `Cost/Normalise` give proposition 3.2
as far as it holds — normalisation in at most m rounds to an
irreducible path-sum, at a cost polynomial in n + m for each fixed
order — and `Cost/Excluded` shows why [Case] and non-linear quotients
are left out (a single step can raise the order).  `Cost/Identity`,
`Cost/Restriction` and `Cost/Corollary` decide whether a circuit over
{H, S, CZ} is the identity, and whether two are equivalent, at a cost
polynomial in n + |C| (corollary 4.4 and the abstract's claim);
`Cost/Gauss`, `Cost/Gauss/Correct` and `Cost/Gauss/Corollary` do the
same for the paper's gate set {H, CNOT, R_k} at level ≤ 2 by its own
route, Gaussian elimination (section 4.1) written in the monad and
run in lockstep with `Gauss`'s, at a cost at most
398 (n + |C| + 3)^11; `Cost/Gauss/Total` computes the level in the
monad too, so that the decision answers for every circuit (declining
above level 2), and `Cost/Corollary/Volume` bounds equivalence in the
volume for {H, S, CZ}; `Cost/Interpreter` is corollary 2.15's time half.  `Reorder/Commute`,
`Full/Order2` and `Cost/Irreducible` show that at order 2 — every
Clifford circuit's restriction — a path-sum no linear rule reduces is
irreducible under all of figure 2, so the normaliser's outputs are
normal forms of the whole calculus and proposition 3.2 holds for it
there; `Full/Order2/Sharp` shows this fails at order 3.

**Section 4: incompleteness, and the remedy.**  `CRK/WithX` adds the
X gate the paper's figure needs; `Examples/Incomplete` proves the
paper's Clifford+T identity has exactly the irreducible path-sum it
prints (`Full/Obstruction` certifies irreducibility cheaply), so normal
forms are not unique.  `Examples/ValidationIncomplete` gives two
equivalent level-3 circuits whose miter's restriction no rule reduces,
so translation validation is incomplete beyond Clifford, though
complete at level 2.  `Expand` and `CRK/Expand` formalise the paper's
remedy — reduce, then expand the remaining variables — as a sound and
complete decision for every path-sum and every pair of circuits,
exponential and never expanding on Clifford inputs; `Gauss/Single` and
`Polynomial/SubstVar` make the closed restriction cheap to compute.
Footnote 2's logical half (unique normal forms would make expansion
unnecessary) is proved.

**Footnote 2: the reduction from unsatisfiability.**  `Hardness/CNF`,
`Hardness/Netlist` and `Hardness` compile every CNF formula φ into a
Clifford+T circuit of linear size that is the identity on the inputs
whose ancillas are |0⟩ exactly when φ is unsatisfiable — the reduction
behind "equivalence checking of reversible circuits is co-NP-complete".
`Hardness/Certificate` gives membership as a certificate check (an input
the two circuits disagree on, found by a counted simulation);
`Hardness/Prepared` and `Hardness/Conditional` show that were normal
forms unique, normalising the reduction's path-sum would decide
unsatisfiability; and `Hardness/Blowup` that the hypothesis would give
the normal forms of x₁ ∨ … ∨ x_n an odd coefficient on every one of
the 2^n − 1 nonempty input monomials.  Machine models, running times,
complexity classes and P = co-NP are not formalised.

**Section 5.2: the quantum Fourier transform.**  `CRK/Controlled`
builds controlled rotations from {H, CNOT, R_k} and proves them the
diagonal e^{2πi x_c x_t/2^k}; `CRK/Trace` reads a circuit's phase and
outputs path by path.  `QFT/Circuit`, `QFT/Spec` and `QFT` prove, for
every n with n + 1 ≤ M, that the Nielsen–Chuang circuit with its
final wire reversal is the paper's specification
|x⟩ ↦ 1/√2^n Σ_y e^{2πi [x][y]/2^n} |y⟩ — through the amplitudes, not
by running figure 2.  `QFT/Unitary` shows the specification unitary
exactly when n ≤ M, `QFT/Relabel` that the final permutation is a
relabelling of the outputs and cannot be dropped, `QFT/Count` the gate
counts behind table 2 (n² Clifford gates: 256 and 961), and
`Examples/QFT` the instances of table 2.

**Section 5.2: n-bit Toffoli gates.**  `Classical` treats path-sums
without path variables whose outputs compute a Boolean function (a
path-sum "computes" F), and their composition; `CRK/Path` reads a
circuit along one path; `Toffoli/Gate`, `Toffoli/Arith` and `Toffoli`
prove the seven-T Toffoli circuit on any three wires of any circuit is
the classical Toffoli gate, at every precision.  `Toffoli/Netlist`,
`ToffoliN/Chain`, `Ancillas` and `ToffoliN` prove the paper's
construction of Toffoli_n — 2(n − 3) + 1 Toffoli gates and n − 3
ancillas — correct for every n ≥ 3: on the inputs whose ancillas are
|0⟩ it computes x_n ⊕ x₁⋯x_(n−1), and it leaves the ancillas clean.
Its qubit (the wires its gates touch, as the tool counts them),
path-variable and T counts reproduce table 2's rows Toffoli50 and
Toffoli100; its Clifford count is eight per Toffoli gate where the
table has nine.  `ToffoliN/Tool` builds the circuit the paper's tool
verified — the same chain, each Toffoli gate by the tool's
sixteen-gate circuit and the uncomputing one by its adjoint — and
proves it ≋ the circuit above, hence correct and clean, with table
2's rows in all four columns; `ToffoliN/Feynman` proves it is the
tool's `toffoliN` gate for gate, for every n ≥ 3, and
`ToffoliN/Wires` that both circuits touch every wire.

**Section 5.2: the Maslov decomposition.**  `RelativePhase` treats
path-sums that compute a permutation up to a diagonal phase, their
composition, their adjoints, and the sandwich lemma: a gate, any
circuit leaving its wires alone, and the gate's adjoint cancel their
phases.  `Maslov/Gate` and `Maslov/Gate4` are Maslov's relative-phase
Toffoli gates (figures 3 and 4 of his paper; the second is the paper's
tool's `rToffoli4`), each proved to compute the Toffoli function up to
an exact phase, with `Maslov/Arith` and `Maslov/Eighths` (sums of
eighth roots of unity by computation).  `Maslov/Chain` and `Maslov`
prove the decomposition the paper's tool builds — a chain of
relative-phase Toffoli-4 gates on ⌈(n − 3)/2⌉ ancillas around a CNOT,
or at odd n around the tool's Toffoli circuit — correct for every
n ≥ 3: its phases cancel exactly on every input, and on the inputs
whose ancillas are |0⟩ it is Toffoli_n, leaving them clean.
`Maslov/Feynman` proves it is the tool's `maslovToffoli` gate for gate,
for every n, and `Maslov/Wires` that it touches every wire; its counts
are table 2's rows Maslov50 and Maslov100 in every column.

**Section 5.2: the out-of-place adder.**  `Adder/Binary` is ripple-carry
addition on bit vectors, `Reversible` circuits of Toffoli and CNOT gates
read classically (with Bennett's compute-copy-uncompute lemma), and
`Adder/Layout`, `Adder/Ripple`, `Reversible/Expand` and `Adder/Circuit`
build the adder on 5n wires with 4(n − 1) Toffoli gates, each expanded
into the seven-T circuit.  `Adder/Spec` builds the specification by
symbolic addition, as the paper does, and `Adder` proves for every n
that on the inputs whose carries and temporary register are |0⟩ the
circuit is that specification and leaves them clean.  The paper's own
circuit is the one its tool, Feynman, generates: `Adder/CarryRipple`
(its netlist, which adds modulo 2^n), `Toffoli/Depth3` (its sixteen-gate
Toffoli circuit) and `Adder/Tool` formalise it and prove the same, and
its counts are table 2's rows Adder8 and Adder16 exactly.
`Adder/Feynman` is that circuit literally, uncomputing by the adjoint
of the expanded compute (`Classical/Adjoint`: the adjoint of a circuit
computing a permutation computes its inverse), the same gate list as
the tool's output; `CRK/Qubits`, `Reversible/Wires` and `Adder/Wires`
count qubits as the tool does, as the wires the gates touch.

**Section 5.2: the hidden shift algorithm.**  `HiddenShift/Walsh`
(character sums, the Walsh transform of the Maiorana–McFarland bent
function f(x, y) = g(x) + x·y is 2^m times its dual g(y) + x·y),
`HiddenShift/Sign` and `HiddenShift` prove H O_f̃ H O_f′ H maps |0⟩ to
|s⟩ for every m, every g and every shift s; `HiddenShift/Simulation`
that every complete reduction by figure 2 ends at |x⟩ ↦ |s⟩, and
`HiddenShift/Blocks`, `Track` and `Exists` that one exists — so the
calculus finds |s⟩ without being given the specification —
`HiddenShift/Example` writing one out.  `HiddenShift/Gates`, `Layers`,
`Circuit` and `Symbolic` do the same for figure 3's circuits over
{H, CNOT, R_k} — oracles built from Z, CZ and CCZ gates, the fixed
shift (|0⟩ ↦ |s⟩) and the symbolic one (|0⟩|s⟩ ↦ |s⟩|s⟩) — with
`HiddenShift/Reduces`, `Ancilla/Register` (a register of ancillas) and
`HiddenShift/CircuitExample` (cross-checks); `HiddenShift/TrackX`,
`Engine`, `MainPasses`, `Runs`, `Layout`, `XLayer`, `ExistsCircuit`
and `ExistsSymbolic` show complete reductions exist on the circuits'
own path-sums too, the calculus finding |s⟩ and |s⟩|s⟩ there.
`HiddenShift/Feynman`, `Tool`, `ToolSymbolic`, `ToolCCZ`, `LayersX` and
`Table` formalise the circuits the paper's tool generated (its 2018
`hiddenShift` and `hiddenShiftQuantum`, X a primitive, so 3n path
variables) as functions of its random draws: gate for gate the tool's
lists, correct for every draw, and with table 2's six hidden-shift
rows — qubits, path variables and T gates as printed for every draw,
the Clifford count exactly when the number c of CZ draws satisfies
|s| + 4c = 1719, 2038, 4082 (hidden shift) or c = 430, 521, 1008
(symbolic shift), each attained; the tool's QuickCheck generator is
unseeded, so the table's own draws are unknown.  `HiddenShift/TraceX`,
`ThreeLayers`, `ToolRuns` and `ToolExists` give complete reductions on
the tool's own path-sums, of exactly 3n steps.  `HiddenShift/Bent`
and `HiddenShift/AnyBent` prove the algorithm correct for every bent
function with its dual, as the paper states it, not only for the
Maiorana–McFarland family; `Polynomial/Interpolate` shows every
function on the Boolean cube is a (unique) multilinear polynomial.
`Adder/Expansion` (with `Polynomial/Count`, `Parity`, `Restrict`)
proves the paper's remark that addition's polynomial specification
grows exponentially: every Boolean polynomial computing the carry out
of n-bit addition has 2^n − 1 monomials, so no classical
specification of the adder is smaller.

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
impossible for a path-sum that is the identity.  The precision is
fixed, as in the paper's tool: phases are integer numerators over 2^M
(M = M₀ + 3, for every M₀), and R_k for k > M is read as R_M.  Lemma
4.1 is proved under `WellFormed`, which definition 2.4 implies and which is strictly
weaker.  Three statements are false as printed, and their corrected
forms are proved beside checked counterexamples: lemma 4.2 needs Q odd
at some input, not merely non-zero (Q = 2x₁); proposition 2.14's bound
is max(2, k), not k (a Hadamard's phase ½xy has order 2 whatever k
is); and proposition 2.7's well-formedness claim fails, for
`WellFormed` and for definition 2.4 alike.  Smaller slips: definition
2.6 omits a renaming in the outputs; section 4.1 substitutes Q where
x_i ⊕ Q is meant; example B.1 as printed is the identity, not ω·I; the
fourth line of example 3.4 does not follow from the third; section
5.2's formula for the shifted function f′ drops the shift; and its
adder has 5n qubits for n ≥ 2, as its table and its tool's circuit
say, not the text's 5n − 1 bits.

Not formalised: running times on a machine and complexity classes;
the time bounds for [Case] and non-linear quotients beyond order 2;
and the benchmarks of section 5 as runs of the tool (the QFT, Toffoli, adder and hidden
shift families are proved for every size).
