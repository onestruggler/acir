# Three-qubit Clifford+CS (Bian–Selinger, QPL 2023)

X. Bian and P. Selinger, *Generators and relations for 3-qubit Clifford+CS
operators*, QPL 2023, arXiv:2306.08530.  Table 1 of qcert.tex:
"three-qubit Clifford+CS, sub-presentation in U₈".

## Statement

* `Syntax.lean`: the generators 𝒳 = {i, K₀, K₁, K₂, S₀, S₁, S₂, CS₀₁, CS₁₂}
  of Theorem 3.1 and the relations of Figure 2: (C1); (C2)–(C4) for each
  qubit `q : Fin 3`; (C5)–(C11) for each pair of adjacent qubits
  `(j, j + 1)`, `j : Fin 2`; (C12)–(C17); and the monoidal relations of part
  (e) ("the scalar `i` commutes with everything, and non-overlapping gates
  commute"), spelled out as: `i` commutes with every generator; one-qubit
  gates on different qubits commute; gates on qubit 0 commute with `CS₁₂`
  and gates on qubit 2 with `CS₀₁`.  The derived gates of Section 2.1
  (`X = K S S K i`, the controlled not `K_t CS CS K_t i`) are abbreviations.
  Words are in the order of matrix multiplication, as in the paper.
* Circuit pictures: qubit `q` is drawn at height `2 - q` (three wires), and
  in the two-wire relations of part (c) the upper qubit `j` of the pair at
  height 1, the lower qubit `j + 1` at height 0.  `\controlled{\notgate}{x,t}{c}`
  is the controlled not with target at height `t` and control at height `c`.
* `Semantics.lean`: K = (1/(1+i))[[1,1],[1,-1]], S = diag(1, i),
  CS = diag(1,1,1,i); `K₀ = K ⊗ I ⊗ I`, … (`tensor`), `CS₀₁ = CS ⊗ I`,
  `CS₁₂ = I ⊗ CS`, the scalar `i` as `i I`.  An 8 × 8 matrix is indexed by
  `Fin 8`, `|q₀ q₁ q₂⟩` at index `4 q₀ + 2 q₁ + q₂`.  `sem` lands in `U(8)`,
  `semU` in `U₈(ℤ[1/2, i])`.
* `Theorem.lean`: `theorem_3_1 : IsSubPresentationOf Rel sem` and
  `theorem_3_1_U : IsSubPresentationOf Rel semU`.

## Proofs

* Soundness of every relation (`Soundness.lean`) by `decide +kernel`, with a
  column-by-column evaluator over ℤ[ω] (`Eval.lean`; `K = ω⁷ H`).  This also
  checks the transcription of Figure 2 (as read from the pictures)
  against the matrices.  `grouplike`: every generator has an inverse.
* Completeness (`Completeness.lean`): the translation `f` into the one- and
  two-level generators of `U₈(ℤ[1/2, i])` (`Translation.lean`) respects the
  interpretation (`lift_f`, decided by an evaluator for the one- and
  two-level matrices); with the presentation of `U₈(ℤ[1/2, i])` (their
  Theorem 2.1, `QCert.BianSelingerUn.presentation 8`) and the
  Reidemeister–Schreier theorem (`QCert.reidemeister_schreier`, proved in
  `QCert/CliffordT2/ReidemeisterSchreier.lean`), any coset data satisfying
  hypotheses (a) and (b) gives completeness (`complete_of_rsData`).

## Remaining `sorry`

* `Completeness.rsData`: the existence of the Reidemeister–Schreier coset
  data with hypotheses (a) and (b).  What the paper's proof consists of
  (Sections 3.1, 4 and 6): `CliffordCS(3)` is the subgroup of `U₈(ℤ[1/2, i])`
  of determinant `±1`, of index 2; the Reidemeister–Schreier theorem is
  applied "recursively", "through a number of intermediate
  representations" (the folders `Step1` – `Step8` of their code), and the
  resulting thousands of relations, "some … more than 50,000 generators",
  are reduced to Figure 2 by rewriting to an almost-normal form built from
  normal forms of the finite subgroups of Section 4 (`W`, `Q`, `C`, `CQ`,
  `P`, `D`, `PD`, `QD`, `CQD`, `K₀D`, `K₀CD`, `K₀W`) and the relations of
  Figure 4.  The paper prints none of the coset tables, translations or
  intermediate presentations: all of them live only in the authors' Agda
  code, cited as "[6] Agda code accompanying this paper", available from
  https://www.mathstat.dal.ca/~selinger/papers/downloads/cliffordcs3/ (not
  part of the arXiv source).  It was not reproduced here.  Everything else
  in the completeness argument is proved.

### What porting `rsData` would involve

The current task excludes consulting Agda formalizations. Completing this
row therefore requires independently constructing and verifying suitable
coset data, or another completeness proof. The historical inventory below
is not a Lean proof and does not discharge `rsData`.

**Source.** All the data is in the authors' Agda code (CC BY 2.0), at
https://www.mathstat.dal.ca/~selinger/papers/downloads/cliffordcs3/cliffordcs3.tgz
(SHA-256 `ff650f651355240ab99e54777c1befe02715386853b9e341b4e67ab320d8620b`;
118 Agda files, 4.5 MB).

**How their proof is assembled.** `Completeness.agda` composes nine
presentations by the Reidemeister–Schreier theorem.  Only Step 3 uses it
with cosets (two, `I` and `I₁`, the index-2 subgroup).  Every other step
uses the simplified version, a Tietze transformation given by
translations both ways.  Each step proves hypothesis (a) for the
generators and hypothesis (b) for the relations of one presentation,
translated into the other; those hypothesis-(b) proofs are the
derivations a port would have to replay.

**The stages.** Counts are the constructors of each relation type,
measured on the files.  Lengths are letters on both sides together.

| Stage | Files | Generators | Relations | Length |
|---|---|---|---|---|
| Statement | `Theorem.agda` (`TwoLevel.Rel`) | one- and two-level, 8 indices | 19 families | ≤ 9 |
| Step 1 | `Step1/` | the same, indices ordered | 33 families | ≤ 9 |
| Step 2 | `Step2/Theorem.agda`; (b) in `Step2/hypB/ax*.agda` (28 files, 0.84 MB) | 9 (`i₀`, `K₀₁`, `X₀₁` … `X₆₇`) | 48 | ≤ 8 |
| Step 3 | `Step3/Rel.agda` (0.5 MB); `Step3/Main.agda` (2 cosets: 28 cases of (a), 96 of (b)); `Step3/PD3`–`PD7` (normal forms of the finite subgroups, 0.73 MB) | 28 gates of `Gate.agda` | 3192 | ≤ 32 (median 10; 35 369 letters in all) |
| Step 4 | `Step4/` (`Main.agda` 0.3 MB) | 28 gates | 508 | ≤ 16 |
| Step 5 | `Step5/` | 28 gates | 401 | ≤ 18 |
| Step 6 | `Step6/` | 28 gates | 203 | ≤ 18 |
| Step 7 | `Step7/` | 28 gates | 115 | ≤ 18 |
| Step 8 | `Step8/` (`Swap*.agda`, `Monoidal.agda`; 0.43 MB) | Figure 2's 9 | 54 (`Theorem.agda`, `CliffordCS.Rel`) | ≤ 18 |

**Word lengths.** No stated relation is longer than 32 letters.  The
paper's "more than 50,000 generators" must therefore count words that
arise inside the hypothesis-(b) derivations, where a relation is
translated and rewritten.  Those words were not measured.

**Cost.** The authors report about 120 minutes to check it with Agda 2.6.4.
A port would replay the derivations of Steps 1–8 as certificates.  At the
cost measured for CliffordT2 (about a millisecond per rewriting step in
the kernel), the size of the job is set by the number of steps those
derivations take, which has not been measured.
