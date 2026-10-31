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

## Checked coset construction

`Cosets.lean` supplies the two cosets and proves both hypotheses of
Reidemeister–Schreier. `Completeness.rsData` packages this data, completing
Theorem 3.1. There are no unfinished proofs in this development.

* `Two/Completeness.lean` proves completeness on a pair of qubits from the
  presentation of U₄. It supplies the checked two-qubit equalities used
  in the three-qubit derivations.
* `Macro8.lean` proves that all relations of U₈ follow over a macro
  alphabet: the seven transpositions along the Gray path
  `6, 4, 0, 2, 3, 1, 5, 7`, the phase on state 7, and the two-level K on
  states 5 and 7.
* `Cert/` derives the 98 macro-relation/coset obligations and nine
  generator round trips from Figure 2. The finite block groups,
  disjoint-support commutations, controlled-face actions, and permutation
  calculus produce rewrite certificates. The face actions transport the
  proved two-qubit theorem only after checking every relation of that
  action.
* `Cosets.b2OK_true` and `Cosets.aOK_true` check that the certificate
  endpoints are exactly those of the action. `hyp_b` transports the
  macro derivations; `hyp_a` checks the translation of each generator.

This is an independent construction from the paper and the existing Lean
results. It does not import the authors' Agda proof. Python uses numerical
matrices to find candidate words, but every equality used by the theorem
is rechecked in Lean: either by an exact two-qubit evaluator or by replay
of derivations. No Python result is admitted as an axiom.

## Building and regeneration

From `Lean/`:

```sh
./check.sh QCert/CliffordCS3/Theorem.lean QCert/Audit.lean
```

The certificate checks are substantial on a first build. In the 31 October
WSL check, the pair batches took roughly three minutes each, with four
running at once. The largest final derivation batch took about twelve
minutes and 17 GB of resident memory. Subsequent builds reuse these
checked modules.

The generated Lean certificate files suffice to build. Regenerating them
requires Python 3 and NumPy, from `QCert/CliffordCS3/gen/`:

```sh
python3 build_w.py
python3 pc.py
python3 complete3.py
python3 roundtrip3.py
python3 run_b1_8.py
python3 threeemit.py
python3 finalize3.py
```

The first two commands build reusable finite-group search caches. The
remaining commands construct the action obligations, round trips, macro
presentation, and Lean certificate files. The generated two-qubit
certificates have their own generator, `twoemit.py`. Search caches and
logs are not needed for Lean verification.
