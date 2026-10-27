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
  Theorem 2.1, `bsPresentation`) and the
  Reidemeister–Schreier theorem (`QCert.reidemeister_schreier`, proved in
  `QCert/CliffordT2/ReidemeisterSchreier.lean`), any coset data satisfying
  hypotheses (a) and (b) gives completeness (`complete_of_rsData`).

## Remaining `sorry`s

* `Completeness.bsPresentation`: Theorem 2.1 of the paper (the presentation
  of `U₈(ℤ[1/2, i])`), the statement `QCert.BianSelingerUn.presentation 8`
  of the folder `QCert/BianSelingerUn/` (another agent's), restated here
  because that module did not build at the time (its `MainK.lean` failed);
  replace by `BianSelingerUn.presentation 8` once it builds.
* `Completeness.rsData`: the existence of the Reidemeister–Schreier coset
  data with hypotheses (a) and (b).  The paper gives no coset table (only
  that the subgroup has index 2, the matrices of determinant ±1); its proof
  is the authors' Agda code ("a sequence of multiple applications of the
  Reidemeister–Schreier theorem passing through a number of intermediate
  representations", Steps 1–8, thousands of relations of up to 50,000
  generators), which is not part of the arXiv source and was not
  reproduced.  Everything else in the completeness argument is proved.
