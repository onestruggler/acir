# Blake (FSCD 2026): six fragments, minimal and complete

C. Blake, *Simpler presentations for many fragments of quantum circuits*,
FSCD 2026, arXiv:2602.09874 — Table 1 row "six fragments — minimal,
complete" of `qcert.tex`.  Formalised from the paper alone.

The main statements are in [`Theorems.lean`](Theorems.lean).

## What is proved

| fragment | rules | soundness | completeness (Theorem 22) | minimality (Theorem 37) |
|---|---|---|---|---|
| qubit Clifford Cliff₂ | Figure 2, 8 rules | proved | **transferred** from Selinger (`clifford_complete_of_source`, proved; `clifford_complete` through `QCert.SelingerClifford.presentation`) | **proved**, all arities |
| real Clifford RCliff₂ | Figure 3, 10 rules | proved | **transferred** from Makary–Ross–Selinger (`realClifford_complete_of_source`, proved; `realClifford_complete` through `QCert.RealStabilizer.presentation`) | **proved**, all arities |
| qutrit Clifford Cliff₃ | Figure 4, 10 rules, (E) corrected | proved | **transferred** from Li–Mosca–Ross–van de Wetering–Zhao refined by `ω₁₂` (Lemma 50 proved; `qutritClifford_complete_of_source`, proved; `qutritClifford_complete` through `QCert.QutritClifford.complete`) | **proved** up to 2 wires |
| Clifford+T CliffT₂ | Figure 5, 11 rules | proved | **transferred** up to 2 qubits: two from Bian–Selinger, one and none from Greylyn (`cliffordT_complete_of_source`, proved; `cliffordT_complete` through `QCert.CliffordT2.theorem_2_1` and `QCert.Greylyn.presentation`) | **proved** up to 1 wire, and (CPh), (B), (CZ) independent |
| Clifford+CS CliffCS₂ | Figure 6, 14 rules | proved | **proved** up to 3 wires (`cliffordCS_complete`), with complete source proofs on two and three wires | **proved** up to 2 wires, and (I) independent |
| CNOT-dihedral CNOTdihe₂ | Figure 7, 11 rules | proved | **transferred** from Amy–Chen–Ross (`complete_of_source`, proved; `complete` through `QCert.CNOTDihedral.presentation`) | **proved**, all arities |

Every rule of every figure, and every law of the symmetry, is checked
against the semantics of Section 3 by an exact computation.  Every separator
of Figure 8 that the paper gives is checked, and Theorem 37 is proved in
full as stated.

## Files

* `Basic.lean` — PROP presentations on the framework's circuits: the swap as
  a two-wire gate with the laws of the symmetry (`Sym`), presentations
  (`PropPresentation`: a swap and an indexed family of axioms), derivability
  from a selection of axioms (`Derives`), Definition 23 (`Independent`,
  `IndependentIn`, `Minimal`), Definition 24 (`MinimalUpTo`), Definition 9
  (`Complete`, `CompleteUpTo`), the truncation of Remark 14
  (`derives_truncate`, `independentIn_upTo_iff`, `minimalUpTo_iff`), models
  of the PROP structure and Lemma 25 (`Model`, `independent_of_model`).
* `Models.lean` — the separators: weighted counts (`Weights`, Definitions
  26, 28–30 and 35: `?g` in `Occ`, `#{…}_[m]` in `ZMod m`, `arg det_k` in
  `ZMod 8` in units of `π/4`) and projective matrix models (`projModel`,
  `independent_of_proj`, Definitions 32–34).
* `Exact.lean` — `ZQuartic p q = ℤ[x]/(x⁴ - p x² - q)`; ℤ[ω] (`ZOmega`) and
  ℤ[ζ₁₂] (`ZZeta`) with their embeddings into `ℂ` and into the framework's
  ℚ(ω), ℚ(ζ₁₂), complex conjugation, `√2`, `√3`.
* `Trie.lean` — a kernel evaluator: matrices stored as tries of rows,
  generators applied by linear combinations of subtries, with the bridge
  `den_evalRows : den (evalRows O n w) = O.eval n w`.
* `Scaled.lean` — gate matrices as `1/√2`- or `1/√3`-scaled integer matrices;
  equations and unitarity decided over the integers.
* `Qubit.lean`, `Qutrit.lean` — the interpretations of Section 3.1
  (Definition 13) and Section 3.2 (Definition 17).
* `<Fragment>/Syntax.lean` (gates, shortcuts of Figure 9, one constructor per
  rule), `Semantics.lean`, `Soundness.lean`, `Minimality.lean` for
  `Clifford`, `RealClifford`, `QutritClifford`, `CliffordT`, `CliffordCS`,
  `CNOTDihedral`.
* `Engine.lean`, `Comm.lean`, `Derive.lean` — derivations: moving them up
  and padding them (`derivable_shift`, `derivable_pad`), the interchange law
  (`comm_apart`: generators on disjoint wires commute), and a checker that
  replays a derivation given as rewrite and exchange steps (`derive`,
  decided by `decide +kernel`); a run of exchanges moving one generator is
  one step (`slide`), which shortens long derivations (the qutrit ones from
  21 020 steps to 3 239, which the kernel then checks in minutes).
* `Transfer.lean` — Theorem 21 (`complete_of_transfer`), Lemma 20
  (`derivable_map_of`), and renaming gates (`derivable_rename`).
* `Cross.lean` — the semantic half of an encoding (Definition 18): circuits
  of two gate sets compared on row tries (`sem_eq_cross`), a substitution
  preserving every gate's matrix preserves every circuit's
  (`GateSubst.sem_map`), real matrices read over `ℂ` (`GateSem.sem_map_of`),
  and Theorem 21 for a source semantics in another monoid
  (`complete_of_transfer_map`).
* `Flat.lean` — Theorem 21 for a source whose letters are flat (one letter
  per gate and qubit, or one- and two-level matrices of a fixed dimension),
  with matrices over `ℚ(ω)` indexed by `Fin (2ⁿ)`: the encoding preserves
  the semantics as soon as it does on each generator (`flat_sem`), and
  `complete_of_flat`, `derivable_lift_comp` (Lemma 19 for such an
  encoding).
* `FlatRefine.lean` — Lemma 50 for a flat source whose scalars are the powers
  of `i`: the refinement by a central `w` with `w² = i` (`RRel`), every
  refined word `wᵃ` times a source word (`extract`), and completeness of the
  refinement from the source's (`refine_complete`), the hypothesis "no
  hidden phases" proved by a parity argument in `ℚ(ω)` (`parity`: the
  source's matrices have their entries in `ℚ(i)`); `ℚ(ω) → ℂ` injective
  (`toC_injective`).
* `Subst.lean` — encodings and decodings (Definition 18) as substitutions
  of circuits for gates (`GateSubst`), extended to PROP morphisms; the
  structural rules carried (`lift_map`), Lemma 20 (`derivable_map`) and
  Lemma 19 (`derivable_comp`).
* `Clifford/Transfer.lean`, `Clifford/Derivations.lean`,
  `Clifford/Completeness.lean` — Theorem 22 (1): the encoding and decoding
  of Table 3 (with the swap encoded by its `H`/`CZ` circuit, Selinger's
  presentation having no swap), the semantics preserved (`sem_E`), the
  derivations of Appendix A, the decoded relations C1–C15 (Appendix G.1,
  `rel_derivable`) and the round trips (Appendix F.1, `DE`).
* `RealClifford/Transfer.lean`, `RealClifford/Derivations.lean`,
  `RealClifford/Completeness.lean` — Theorem 22 (2), likewise from Makary,
  Ross and Selinger's presentation (Appendices B, F.2, G.2); their real
  orthogonal matrices are read over `ℂ`.  The decodings of R13–R16, which
  the paper leaves to be mimicked from C12–C15, replay Appendix A's
  derivations in RCliff₂ and derive R14–R16 from them.
* `QutritClifford/Refine.lean`, `QutritClifford/Transfer.lean`,
  `QutritClifford/Derivations.lean`, `QutritClifford/Completeness.lean` —
  Theorem 22 (3): Li et al.'s presentation refined by the new scalar `ω₁₂`
  with `-ω = ω₁₂¹⁰` (Appendix I) and Lemma 50 for it (`refined_complete`,
  "no hidden phases" proved by the parity of the powers of `ζ₁₂` in
  `ℚ(ζ₁₂)` over `ℚ(ω)`), the encoding and decoding of Table 3 with the phases
  of `H` corrected (`sem_E`), the derivations of Appendix C, the decoded
  rules C1–C18 and `ω₁₂¹² = 1` (Appendix G.3, `rel_derivable`) and the round
  trips (Appendix F.3, `DE`).
* `CliffordCS/Transfer.lean`, `CliffordCS/Derivations.lean`,
  `CliffordCS/Completeness.lean` — Theorem 22 (5) with no wire and on one
  wire, from Bian and Selinger's presentation of `Uₘ(ℤ[½, i])` in
  dimensions `1` and `2` refined by `ω` (`FlatRefine`); the paper does not
  treat these widths.
* `CNOTDihedral/Derivations.lean` — every relation of Amy, Chen and Ross
  (`QCert.CNOTDihedral.Rel`) derived from Figure 7 (Appendix H); generated
  from derivations found by a search (`gen/`: `run_all.py`,
  `gen_cnot.py`; regenerating reproduces the file).
* `CNOTDihedral/Completeness.lean` — the transfer, and Theorem 22 (6) as a
  presentation (`CNOTDihedral.presentation`: `IsSubPresentationOf` on every
  number of wires).
* `CliffordT/Transfer.lean`, `CliffordT/Derivations.lean`,
  `CliffordT/Completeness.lean` — Theorem 22 (4): on two wires from Bian and
  Selinger's presentation read reversed (Appendices D, F.4, G.4), on one
  wire and none from Greylyn's presentation in dimensions `2` and `1`.
* `Theorems.lean` — the statements.

General lemmas that a framework could host (they are in this folder, the
framework being fixed): `Ops.eval_shift`, `Ops.eval_pad`, `Ops.comm1/2/3`,
`Ops.scalar_up` (the structural rules for `GateOps`, as `GateSem.lift_sound`
has them for `GateSem`), `ZQuartic`, and the evaluator of `Trie.lean`.

## Conventions and modelling decisions

* **Wires and order.**  Wire `0` is the bottom wire of a diagram (the last
  tensor factor), so a two-wire gate's top wire is wire `1`: the CNOT has its
  control on wire `1`.  Circuits are words in operator order; the paper's
  diagrams are read left to right with `seq` (`seq [c₁, …, cₖ]` applies `c₁`
  first).  A gate drawn on non-adjacent wires is the PROP shortcut of
  Figure 9 ((1), (2)): conjugation by swaps; a gate drawn upside down is
  conjugated by the swap.
* **The PROP.**  The framework's `Lift` gives the PRO structure (interchange,
  scalars on every wire).  The symmetry is a two-wire gate `swap` with the
  rules `Sym`: `σσ = id` and the naturality of the block swap `σₙ` for every
  generator (Figure 1); naturality for `σ` itself is the Yang–Baxter
  equation.  These rules are part of every theory and never counted as
  axioms; `Independent ρ` removes only the fragment rule `ρ`.  Each fragment
  has a single scalar generator, so scalars commute.
* **Truncation (Remark 14).**  A derivation on `n` wires uses only axioms on
  at most `n` wires (`derives_truncate`), so an axiom is independent as soon
  as a model satisfies the other axioms on at most as many wires.  The
  separators of Figure 8 are used this way, and several of them are **not**
  models of the whole rule set: `?ω₈` fails on (E), `?H` and `?S` of Cliff₂
  fail on (CZ), `#{CNOT, SWAP}_[2]` (for Cliff₂'s (CZ)) fails on the
  three-wire (I), `[CS := CS·Z₀]∼` fails on (SH₁)–(SH₃), and so on.  This is
  the paper's own argument ("an n-wire axiom can be tested inside the
  subsystem generated by axioms of arity at most n"), and
  `PropPresentation.independent_of_model` builds it in.
* **Minimality up to k wires** (Definition 24) is stated as in the paper,
  relative to the axioms on at most `k` wires; `minimalUpTo_iff` shows it is
  the independence (in the full rule set) of every axiom on at most `k`
  wires.
* **Projective substitutions** (Definition 34) are realised as matrices over
  ℚ(ω) (ℚ(ζ₁₂) for qutrits) modulo units, through ℤ[ω] (ℤ[ζ₁₂]) with the
  Hadamard scaled by `√2` (`√3`), a unit there.  On the matrices of circuits
  this is the paper's quotient by global phases; the substituted gate gets
  the matrix of the substituted circuit (`csz_eq`, `cszz_eq`, `sxZ_eq`).
* **arg det_k** (Definition 35) is a weight table in `ZMod 8` (units of
  `π/4`); the docstrings give the determinants it comes from.
* **Semantics.**  `GateSem` over `ℂ` with the paper's matrices (Definitions
  13 and 17), proved unitary; `ω₈ = (1 + i)/√2` (the framework's `ω`),
  `ζ₁₂ = (√3 + i)/2 = e^{iπ/6}` (`ZZeta.ζ12_eq_exp`).  Equations are decided
  over ℤ[ω], ℤ[ζ₁₂] by `decide +kernel` on row tries and carried to `ℂ`.

## Errors found in the paper

* **Figure 4, rule (E) of Cliff₃.**  Printed as
  `S H S = H H H S S H H H ω₁₂⁷`; with the semantics of Definition 17 the
  left side is `-1 = ω₁₂⁶` times the printed right side
  (`QutritClifford.E_printed_unsound`, proved).  The rule holds with `ω₁₂`
  in place of `ω₁₂⁷`, and `QutritClifford.Ax.E` is that corrected rule.  The
  separators of Figure 8 (c) do not depend on the exponent.

* **Table 3, the qutrit Hadamard.**  Li et al.'s `H` is
  `(ω² - ω)⁻¹ [ωʲᵏ]`, which is `i` times the `H` of Definition 17, so
  `D(H) = H ω₁₂³` and `E(H) = H ω₁₂⁹`; Table 3 prints the two phases the other
  way round, which preserves neither semantics, and the decoded rule (C4)
  then fails.  The corrected phases are used (`QutritClifford/Transfer.lean`).
* **Appendix C, figures.**  Several lines carry the scalar of the misprinted
  (E) (`ω₁₂⁷` for `ω₁₂`) or drop a scalar; in (ZK) `Z` is drawn `S S'²`,
  which is `Z⁻¹` for Figure 9's `Z = S² S'`; the figure `Kb-CNOT-03` cited in
  (KbCnot) is missing from the sources.  Such lines are corrected by their
  phase or skipped (`gen/driver.py`, `repair`), and every step is still
  derived.
* **Appendix D, the decoded (C19).**  The step from
  `(T† ⊗ T†) CX (1 ⊗ T) CX` to `CS†` cites only the definition
  `CS† = CS³`; it needs Figure 5's rules besides (found by the search).
* **Appendix E, figures (provisional).**  The figure `C5-14` cited in the
  decoded (C5) is missing from the sources; in the decoded (C15) the lines
  drawn as `C15-04` and `C15-07` do not have the matrix of the first line as
  read (in `C15-04` an `H` appears to be missing).  These chains are not yet
  used as printed in a proof; the completed transfer supplies checked
  derivations separately.

## Completeness

The transfer of Section 4 is formalised generically (`Transfer.lean`,
`Subst.lean`, `Derive.lean`, `Cross.lean`, `Flat.lean`, `FlatRefine.lean`)
and carried out for CNOT-dihedral (no encoding needed), Cliff₂, RCliff₂,
Cliff₃, CliffT₂ up to two wires, and CliffCS₂ up to three wires.
Each `X_complete_of_source` takes the source presentation's completeness as
a hypothesis and is proved; `X_complete` instantiates it with the source
formalisation's own theorem.

* Cliff₃: Li et al.'s presentation refined by the new scalar `ω₁₂`
  (Appendix I); Lemma 50 is proved for it, its hypothesis "no hidden phases"
  included (`QutritClifford/Refine.lean`).
* CliffT₂ on two wires: Bian and Selinger's presentation
  (`QCert.CliffordT2`).  Its relations are stated in the order of matrix
  multiplication, and the paper draws each of them left to right, i.e.
  reversed; so the decoding reads source words reversed and the encoding
  reverses circuits, which the semantics allows because every gate's matrix
  is symmetric (`Flat.complete_of_flat_rev`).  Then every decoded relation is
  the paper's own figure, and Appendix D's derivations apply as printed.
  (C15), which the paper draws as (TX) `T X = X T† ω₈`, is Bian and Selinger's
  `(T X)² = ω`; its decoding is derived from (TX) and (X²).
* CliffT₂ on one wire and none: Greylyn's presentation of `Uₘ(ℤ[1/√2, i])`
  in dimensions `2` and `1` (`QCert.Greylyn`), which the paper does not
  treat: `H ↦ H_[0,1]`, `T ↦ ω_[1]`, `ω₈ ↦ ω_[0] ω_[1]`, and back
  `X_[0,1] ↦ H Z H`, `ω_[0] ↦ ω₈ T⁷`, `ω_[1] ↦ T`.
* CliffCS₂ on one wire and none: Bian and Selinger's presentation of
  `Uₘ(ℤ[½, i])` in dimensions `2` and `1` (`QCert.BianSelingerUn`), whose
  scalars are the powers of `i`, refined by a central `w` with `w² = i`
  (`FlatRefine`, Lemma 50 proved); `H ↦ w K_[0,1]`, `S ↦ i_[1]`, and back
  `K_[0,1] ↦ ω₈⁷ H`, `i_[0] ↦ ω₈² S³`, `i_[1] ↦ S`, `X_[0,1] ↦ H S S H`.

The derivations of the appendices are transcribed line by line: every
figure of a derivation is read off the paper's PDF figures
(`gen/figparse.py`; boxes, black and white controls, targets, controlled
boxes, dashed `CS` lines, crossings, scalars; the shortcuts of Figure 9
expanded), every pair of consecutive lines is checked to have the same
matrix (lines off by a power of the scalar are corrected, lines that are
not multiples are skipped and reported), and the step between them is found
by a search modulo commuting gates on disjoint wires (`gen/tsearch.py`,
`gen/tsearch2.py`, `gen/driver.py`) that uses the rules the paper cites
for that step first, then their derived forms (inverse, upside down,
wires reversed, `gen/variants.py`, each derived mechanically), then the
neighbouring steps' rules, and finally relator-style partial rewriting.
Where the paper draws a line upside down (a step `σ w σ = mirror(w)`, or
its three-wire analogue), that move is made mechanically.  A few steps are
split by intermediate lines (`EXTRA` in `gen/cliff2.py`, `gen/cliff3.py`,
`gen/tcliff.py`; for instance Appendix D's (wCNOT), (CSCSCSCS), (SCSd) and
(HSTH) move one `T` or one block at a time), and a few helper equations are
derived first: `dczrev`, `natHi`, `natCXi` for the qutrit decodings; `T6CS`,
`TCS`, `T7CS` (a `T` on the target passes `CS`) for (SCSd) and (HSTH);
`CHup` (the decoded controlled Hadamard of qubit 0 is Figure 9's upside
down) for the decoding of (C20).  Uncited steps: in the decoding lemma of
(C19) the step from `(T† ⊗ T†) CX (1 ⊗ T) CX` to `CS³` cites only the
definition of `CS`; it is the helper `CSdag`, derived from (CSCSCSCS),
(T⁸), (CX²), (C) and (phasegadgetCS).  The figures and chains read from the paper are cached
in `gen/figures.json` and `gen/derivations.json`, the derivations found in
`gen/*_cache.txt`; `python run_cliffd.py && python gen_cliff.py
../Clifford/Derivations.lean` (likewise `run_rcliff.py`/`gen_rcliff.py`,
`run_cliff3.py`/`gen_cliff3.py`, `run_tcliff.py`/`gen_tcliff.py`,
`run_cs.py`/`gen_cs.py`) reproduces the generated files byte for byte.

## Proof dependencies

There is no local `sorry` in this folder. `CliffordCS/W2Complete.lean`
proves the two-wire case using the presentation of `U₄(ℤ[½,i])` and its
scalar refinement, with all decoded relations checked.
`CliffordCS/W3Complete.lean` proves the three-wire transfer from
`QCert.CliffordCS3.theorem_3_1`; the encoding, decoding and relation
derivations are checked. The source theorem's coset data
(`QCert.CliffordCS3.rsData`) is proved by the checked two-coset
construction, so `cliffordCS_complete` has no unfinished dependency.

The other completeness statements have no unfinished dependency.
`clifford_complete`, `realClifford_complete`, `cliffordT_complete`,
`cnotDihedral_complete`, `qutritClifford_complete` and the CliffCS₂ widths `0`, `1`, `2`
(`cliffordCS_complete₀₁_of_source` with `QCert.BianSelingerUn.presentation`)
rest on source theorems that are proved: `#print axioms` gives `propext`,
`Classical.choice`, `Quot.sound` only.

## Building

`./check.sh QCert/Minimality/Theorems.lean` builds this development.
The kernel decisions for the three-wire encoding share a larger local
heartbeat budget (`W3Enc.e_ok`); that check can take over a minute.
`./check.sh QCert/Audit.lean` checks the axioms of these results.

## Typechecking cost

The derivation modules (`*/Derivations.lean`, `CliffordCS/W2Lemmas.lean`,
`CliffordCS/W3Lemmas.lean`) spent nearly all their time elaborating the
step lists: a list literal of 64 or more elements loses the expected type
of its elements, so every `.rw i e b` was elaborated without one, postponed
and retried, at about 0.1 s per element (a 675-step list took 52 s, and
`QutritClifford/Derivations` 328 s with 16 jobs in parallel).  Written with
qualified constructors (`Step.rw i e b`, which `gen/leangen.py` and
`gen/gen_cnot.py` now emit) the same list elaborates in 0.16 s and the
module builds in 37 s (`CliffordT/Derivations` 154 → 63 s).  Qualify dotted
constructors wherever the expected type is not known at that point: long
list literals, operands of `++`, arguments whose type is a metavariable.

`CliffordCS/W3Enc` (the fourteen decisions of `e_ok`, 155 s in a full
build) is kernel-bound on products of 8 × 8 matrices over `QOmega`: a
product costs 512 multiplications of four rationals, about 2 s each in
the kernel.  The scalar letter times a gate is now rewritten to the
scaled gate (`smul_mul_assoc`) and the swaps' three permutation matrices
to one (`permMat_mul`) before the kernel compares entries, which removes
seven products; what remains is the four CNOT lemmas `cx₁₂`…`cx₁₀` (four
products each) and about a second per decision for the operator side.
The next step, if it matters, is integer arithmetic: state the letters as
`invSqrt2 ^ e • (M.map toQ)` with `M` over `ZOmega`, multiply over `ZOmega`
(`Int` arithmetic is cheap in the kernel, `Rat` is not) and compare the
exponents and the integer matrices.
