# Blake (FSCD 2026): six fragments, minimal and complete

C. Blake, *Simpler presentations for many fragments of quantum circuits*,
FSCD 2026, arXiv:2602.09874 — Table 1 row "six fragments — minimal,
complete" of `qcert.tex`.  Formalised from the paper alone.

The main statements are in [`Theorems.lean`](Theorems.lean).

## What is proved

| fragment | rules | soundness | completeness (Theorem 22) | minimality (Theorem 37) |
|---|---|---|---|---|
| qubit Clifford Cliff₂ | Figure 2, 8 rules | proved | stated (`sorry`) | **proved**, all arities |
| real Clifford RCliff₂ | Figure 3, 10 rules | proved | stated (`sorry`) | **proved**, all arities |
| qutrit Clifford Cliff₃ | Figure 4, 10 rules, (E) corrected | proved | stated (`sorry`) | **proved** up to 2 wires |
| Clifford+T CliffT₂ | Figure 5, 11 rules | proved | stated up to 2 qubits (`sorry`) | **proved** up to 1 wire, and (CPh), (B), (CZ) independent |
| Clifford+CS CliffCS₂ | Figure 6, 14 rules | proved | stated up to 3 qubits (`sorry`) | **proved** up to 2 wires, and (I) independent |
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
  decided by `decide +kernel`).
* `Transfer.lean` — Theorem 21 (`complete_of_transfer`), Lemma 20
  (`derivable_map_of`), and renaming gates (`derivable_rename`).
* `CNOTDihedral/Derivations.lean` — every relation of Amy, Chen and Ross
  (`QCert.CNOTDihedral.Rel`) derived from Figure 7 (Appendix H); generated
  from derivations found by a search (`gen_cnot.py`, kept in the scratch
  area).  `CNOTDihedral/Completeness.lean` — the transfer.
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

## Remaining `sorry`s

| statement | paper | what it needs |
|---|---|---|
| `clifford_complete` | Theorem 22 (1) | completeness of Selinger's presentation, and Lemmas 19, 20 (Appendices A, F, G) |
| `realClifford_complete` | Theorem 22 (2) | Makary–Ross–Selinger's presentation, Lemmas 19, 20 (Appendices C, F, G) |
| `qutritClifford_complete` | Theorem 22 (3) | the qutrit Clifford presentation with scalar refinement (Lemma 50), Lemmas 19, 20 (Appendices D, F, G) |
| `cliffordT_complete` | Theorem 22 (4) | Bian–Selinger's two-qubit Clifford+T presentation, Lemmas 19, 20 (Appendices E, F, G) |
| `cliffordCS_complete` | Theorem 22 (5) | Bian–Selinger's three-qubit Clifford+CS presentation with scalar refinement, Lemmas 19, 20 |
| `cnotDihedral_complete` | Theorem 22 (6) | nothing here: the transfer is proved (`cnotDihedral_complete_of_source`); the statement uses `QCert.CNOTDihedral.presentation`, whose completeness is that formalisation's `sorry` |

## Building

`./check.sh QCert/Minimality/Theorems.lean` builds everything (the slowest
module, `CNOTDihedral/Soundness`, about 20 s).
