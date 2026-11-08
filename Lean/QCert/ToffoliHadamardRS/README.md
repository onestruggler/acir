# Amy, Ross, Wesley (2024), by translation into Li–Ross–Selinger

M. Amy, N. J. Ross, S. Wesley, *A Sound and Complete Equational Theory for
3-Qubit Toffoli–Hadamard Circuits*, QPL 2024, arXiv:2407.11152.

A Lean translation of the Agda development
`Examples/Groups/CCX+H-3qubit-RS/`, which proves the paper's theorems by
translation into Li, Ross and Selinger's presentations of `O(8, 𝔻)` and
`L₈` (here `QCert.LiRossSelinger`).  The Lean follows the Agda module for
module, with the same names, the same definitions and the same proof
route, except where noted under "Deviations".  It is independent of
`QCert/ToffoliHadamard/`, the formalization written from the paper, and
does not use it.

## What is proved (`Theorem.lean`)

* `theorem_5_2 : IsPresentationOf R1plus sem1`: `R₁⁺ = Figure 4 ∪ Figure 7
  ∪ {r_K}` presents `O(8, 𝔻)` on `Σ₁` (the Toffoli-K gates, `K_[0,1,2,3]`
  and `CCZ`), with `soundness₁` and `completeness₁`;
* `theorem_6_3 : IsPresentationOf R2plus sem2`: `R₂⁺ = R₁⁺ ∪ Figure 8`
  presents `TofH(3) = L₈` on `Σ₂ = Σ₁ ∪ {H₂}`, with `soundness₂` and
  `completeness₂`;
* `r_K_independent`: `r_K` (Section 5.5, `K₁₂ = X₀ NK X₀ NK`) holds of the
  matrices but is not derivable from `R₁ = Figure 4 ∪ Figure 7`;
* `circuits_5_2`, `circuits_6_3`: the two presentations for the circuits
  of `Circuits/Syntactics` on three wires (`QCert.Lift Circuits.SRel1 3`,
  `QCert.Lift Circuits.SRel2 3`, over the framework's `QCert.Circuit`);
* `unitary₁`, `unitary₂`, `circuits_unitary₁`, `circuits_unitary₂`: all
  four are sub-presentations of `U(8)`;
* `errata`: the printed equations that are false ((33), (97), (100),
  `CCX₁₂ = X_[6,7]`, `(r_CX)`, the alias `(-1)_[0]`, and Section 5.7's
  decomposition of `CCZ`), each refuted by one matrix entry (`Errata`, which
  also checks the corrections not checked elsewhere);
* `gate_matrix`, `gate_matrixH` (`GateMatrices`): each gate denotes its
  usual matrix.

No `sorry`, no new axioms, no `native_decide`, `ofReduceBool` or
`implemented_by`.  `#print axioms` of every theorem above (and of
`soundness₁`, `completeness₁`, `soundness₂`, `completeness₂`,
`gate_matrix`, `gate_matrixH`) gives `[propext, Classical.choice,
Quot.sound]`.

## Module map

| Agda (`CCX+H-3qubit-RS/`) | Lean (`QCert/ToffoliHadamardRS/`) | |
| --- | --- | --- |
| `Gates` | `Gates` | written |
| `Syntactics` | `Syntactics` | written |
| `Engine` | `Engine` | written |
| `Toffoli/Base`, `Lemmas`, `Coxeter` | the same | generated (`gen/mk_toffoli.py`) |
| `Symmetric/CoxeterFrames` (outside the folder) | `CoxeterFrames` | written, with the completeness of the Coxeter presentation proved here |
| `Perm` | `Perm` | written |
| `Lift` | `Lift` | written |
| `Encoding`, `Semantics` | the same | written |
| `Decide` | `Decide` | written |
| `Check` | `Check` | written |
| `Soundness`, `Soundness/Figure7a`, `Figure7b` | the same | written |
| `Congruence` | `Congruence` | written |
| `SoundnessH` | `SoundnessH` | written |
| `Decode` | `Decode` | written |
| `StdMatrices`, `DecMatrices` | the same | written |
| `Completeness` | `Completeness` | written |
| `Derived` | `Derived` | written (generated in the Agda, `mk_derived.py`) |
| `PresentationO8` | `PresentationO8` | written |
| `Push`, `PushMatrices` | the same | generated (`gen/mk_push.py`) |
| `TableMatrices` | `TableMatrices` | written |
| `DecodeH`, `PresentationH` | the same | written |
| `Independence` | `Independence` | written (generated in the Agda, `mk_indep.py`) |
| `Errata` | `Errata` | written |
| `GateMatrices` | `GateMatrices` | written |
| `Entry00` | — | not needed (see below) |
| `Circuits/Syntactics`, `Iso1`, `Iso2` | the same | generated (`gen/mk_circuits.py`) |
| `Circuits/Presentation` | `Circuits/Presentation` | written |
| `DOmega` | `Unitary` | written |
| `Theorems`, `MainTheorem` | `Theorem` | written |

The generators import the Agda generators' modules (`rels`, `targets`,
`model`, `rounds`, `hconj`) from `Examples/Groups/CCX+H-3qubit-RS/gen`, and
write the Lean modules from the same `derivations.json`: the same lemmas in
the same order with the same steps (`mk_toffoli.py`: 21 equations in
`Toffoli/Base`, 210 in `Toffoli/Lemmas`, 28 in `Toffoli/Coxeter`), the same
conjugates `H₂ g H₂` (`mk_push.py`), and the circuit rules read off the
Agda `Syntactics.agda` (`mk_circuits.py`).  Run from `gen/`:

```sh
python3 mk_toffoli.py && python3 mk_push.py && python3 mk_circuits.py
```

With the committed `derivations.json` they reproduce the Lean modules byte
for byte.

## Deviations from the Agda

* **`Sₙ`.**  The Agda reads Coxeter words as circuits of its presentation
  of `S₈` (`Examples/Groups/Symmetric`), whose completeness gives
  `perm-complete` and whose surjectivity gives `stab`.  The Lean library has
  no presentation of `Sₙ`, so `CoxeterFrames` writes Coxeter words as lists
  of indices and proves both facts by one normal form (`frame` of a
  permutation; multiplying by a generator gives the normal form of the
  product, `key`).
* **Deciding values.**  Agda's `refl` on one Boolean (`eqM`) is
  `decide +kernel` on Li–Ross–Selinger's `ListMat.eqS`: each generator of
  `𝒢₈`, and `I ⊗ H`, is `(1/√2)^s` times an integer row operation, so a
  word's matrix is a scaled integer matrix computed by the kernel
  (`Decide`).  The engine's runs are likewise one Boolean (`Engine.check`).
* **Levels.**  `decide` does not accept a statement with a free level, so
  the soundness of Figures 4 and 7 and `r_K` is stated at the levels at which
  it is used (`Soundness`: Figure 4 at levels 0–2, Figure 7 and `r_K` at 1–2)
  rather than at every level.
* **Congruences.**  `Congruence` is `derivable_hom`, soundness of the
  congruence for a reading that is a monoid homomorphism (the framework's
  `derivable_sound` is for readings `FreeMonoid.lift sem`).
* **Surjectivity.**  The Agda's `Conjugation.decompose` (one adjacent
  transposition at a time) is the Lean development's `conjForm_gen` (Lemma
  A.19's decomposition `g ≈ P g₀ P⁻¹` at once) in `PresentationO8.dec_sem`.
* **`Derived` and `Independence`** are written by hand: `Derived` is short,
  and its two derivations are those of `mk_derived.py`; `Independence`'s
  clause tables (`mk_indep.py`) are case splits on the gates (`twist`,
  `fixed`) with a few matrix checks.
* **`GateMatrices`** compares the gates' formulas with the semantics over
  `ℝ`, through the scaled integer matrices of `Decide` (`coefMatches`),
  where the Agda reads the entries in `𝔻` and `ℤ[1/√2]`.
* **`Entry00`** isolates an Agda instance-resolution problem (`Ring Dyadic`
  beside `Ring D`); Lean has no such problem, and `Decide.entryNe` reads the
  entries directly.
* **`DOmega` → `Unitary`.**  The Agda reads both groups in `U₈(𝔻[ω])`
  through ring embeddings; here `O(8, 𝔻)` and `L₈` are subgroups of the
  real `U(8)` already, so the embedding is the inclusion
  (`along_subgroup`).
* **Circuits.**  The Agda's `Circuit.Base` is the framework's
  `QCert.Circuit` (`Gen`, `Lift`).  The Agda proves the reading of circuits
  a group isomorphism (`circuits≅paper`) and composes isomorphisms; the
  framework's `IsPresentationOf` states soundness, completeness and
  surjectivity of a generator-level semantics, so `Circuits/Presentation`
  proves one lemma (`transfer`) that carries a presentation along two
  translations respecting the relations and inverse up to them — the data
  `circuits≅paper` is built from.  In `Iso1`/`Iso2` the readings of the
  paper's words are computed by `simp` (`via`, `by_der`, `defn`, with the
  lemmas `κ_T` … `κ_Ω`) rather than left to definitional unfolding, which
  exhausts Lean's recursion depth on the long words of Figure 7.
* **Words.**  The framework's words are `FreeMonoid`, which is `List`, so
  the Agda's `⟪_⟫`/`flat` between letter lists and tree-shaped words are
  the identity.  Products are written left-nested, as Lean's `*`
  associates.

## Building

```sh
./check.sh QCert/ToffoliHadamardRS/Theorem.lean
```

`Theorem.lean` reaches all 38 modules.  From a clean folder (the
dependencies built), 2 min 30 s wall time under Lake's parallel jobs,
311 s of module time in all; the slowest modules are `Decode` (38 s),
`Circuits/Iso2` (16 s), `Soundness/Figure7b` (15 s), `TableMatrices`,
`Decide` (13 s each), `Circuits/Iso1` (12 s), `Soundness` and
`CoxeterFrames` (10 s each), the rest under 10 s.
