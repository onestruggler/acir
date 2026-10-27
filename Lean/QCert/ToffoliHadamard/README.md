# Amy, Ross, Wesley (2024): three-qubit Toffoli–Hadamard circuits

M. Amy, N. J. Ross, S. Wesley, *A sound and complete equational theory for
3-qubit Toffoli–Hadamard circuits*, QPL 2024, arXiv:2407.11152.  Formalized
from the paper (TeX source, PDF, and its supplement), numbering as printed.

## Statements (`Theorem.lean`)

* `theorem_5_2 : IsPresentationOf R1 sem1` — `R₁` = Figure 4 (`R₀`,
  (1)–(46)) ∪ Figure 7 (`R₈⁴`, (83)–(101)) ∪ `{(r_K)}` presents `O(8, 𝔻)`
  (`O_ZHalf 8`) on `Σ₁` (Theorem 5.2 **with `(r_K)` restored**).
* `rK_independent : ¬ Derivable Fig47 (w [K12]) (w rKrhs)` and
  `theorem_5_2_as_stated_fails : ¬ IsSubPresentationOf Fig47 sem1` —
  `(r_K)` does not follow from Figures 4 and 7, so Theorem 5.2 as stated
  is false (both sides of `(r_K)` have the same matrix).
* `theorem_6_3 : IsPresentationOf R2 sem2` — `R₂ = R₁ ∪` Figure 8
  ((102)–(108)) presents `TofH(3) = L₈` (the orthogonal matrices `N/√2^k`,
  `N` integral; Li–Ross–Selinger's `L 8`) on `Σ₂ = Σ₁ ∪ {H₂}`
  (Theorem 6.3, with surjectivity).

Reviewer's files: `Syntax.lean` (the alphabets `Sym1`, `Sym2`; Figures 4,
7, 8 and `(r_K)`; the abbreviations of Sections 5.3 and 5.6 for
multi-level operators), `Matrices.lean` (the gates of Section 3 as
operators on `|x₀x₁x₂⟩`), `Semantics.lean` (`sem1`, `sem2`, the target
groups), `Theorem.lean`.

## Conventions

* The alphabet is the paper's, one symbol per gate: `X0 … CCZ`, `Kc` for
  `K_[0,1,2,3]`, `S01` … for `σ_{0,1}` …, `H2`.  Words are read left to
  right as matrix products (`⟦u v⟧ = ⟦u⟧⟦v⟧`).
* Qubit `0` is the most significant: the basis vector of `|x₀x₁x₂⟩` is
  `4x₀ + 2x₁ + x₂` (as the paper's multi-level operators require:
  `CCX_{0,1} = X_[6,7]`, `CCZ = (−1)_[7]`).  In the framework's wire
  numbering (wire 0 the least significant digit) paper qubit `j` is wire
  `2 − j`.
* Matrices are defined over any commutative ring with an element `s` for
  `1/√2` (`Matrices.lean`) and taken over `ℝ` with `s = 1/√2`; identities
  are decided over `ℚ(√2)` (`Eval.lean`: each gate as a row permutation,
  row signs or a dense matrix, so that words of hundreds of letters are
  evaluated quickly by `decide +kernel`).

## Errors in the paper (each checked on matrices; `gen/` scripts in scratch)

* **`(r_K)` is missing** from Theorem 5.2's relations (Figures 4 and 7):
  proved independent (`Independence.lean`): interpret each Toffoli–K gate
  `g` as `R⟦g⟧R` with `R = I − J/4` the reflection in the all-ones vector,
  and `K_[0,1,2,3]`, `CCZ` as themselves; every relation of Figures 4 and 7
  holds (Figure 4 is conjugated by `R`, Figure 7 only involves `K_[0,1,2,3]`,
  `CCZ` and permutation gates, which commute with `R`), while `(r_K)` fails
  (entry `(0,0)`: `−1/4` against `1/2`).
* (33) is printed `CCX_{0,1} ≈ σ_{1,2} CCX_{0,2} σ_{0,2}` (false); used as
  `σ_{1,2} CCX_{0,2} σ_{1,2}`.
* The alias `(−1)_[0] = X₀ X₁ CCZ X₁ X₀` (Section 5.6) is `(−1)_[1]`; used as
  `X₀ X₁ X₂ CCZ X₂ X₁ X₀`.  (With the printed alias (85), (94), (97), (98),
  (101) are false.)
* (97) is printed `X_[0,1] K_[0,1,2,3] ≈ K_[0,1,2,3] X_[0,1] (−1)_[1] (−1)_[3]`
  (false); used as `… ≈ K_[0,1,2,3] X_[1,3] (−1)_[1] (−1)_[3]`, the relation
  (4a) of Li–Ross–Selinger it transcribes.
* (100) is printed `K_[0,1,2,3] K_[1,3,4,5] ≈ K_[1,3,4,5] K_[0,1,2,3]` (false:
  they do not commute); used as `… ≈ K_[2,3,4,5] K_[0,1,2,4]`, the relation
  (5a) of Li–Ross–Selinger.  The same two slips are in Figure 5 ((63),
  (66)), Figure 6 ((78), (81)) and Figure 10 ((125), (128)).
* `(r_CX) : CX_{0,1} ≈ X_[2,6] X_[3,7]` (Section 5.5) is false
  (`X_[2,6] X_[3,7] = CX_{1,0}`; `CX_{0,1} = X_[4,6] X_[5,7]`); it is not part of
  the final presentation.
* The decomposition `CCZ = K_{1,2} CZ_{1,2} X₀ K_[0,1,2,3] X₀ CZ_{1,2}
  K_[0,1,2,3] X_[5,6]` of Section 5.7 is false (the other one,
  `K_[0,1,2,3] = (K_{1,2} CCZ)³ X_[5,6]`, holds); not part of the presentation.
* Section 5.5 says `CCX_{1,2} = X_[6,7]`; it is `CCX_{0,1} = X_[6,7]` (as
  stated in Section 5.0).
* Ambiguity: the abbreviations `X_[1,3]`, `X_[0,4]` (Figure 7) are not
  spelled out; `X_[a,b] = X_[a,a+1] X_[a+1,b] X_[a,a+1]` is used (relation
  (76) generalised).  `K_[a,b,c,d]` and `(−1)_[c]` follow Section 5.3.

## What is proved

* Soundness of `R₁` and `R₂` (`Soundness.lean`), every relation decided on
  `8 × 8` matrices; grouplike (every letter a unit modulo `R₁`).
* Independence of `(r_K)` and the failure of Theorem 5.2 as stated.
* **Section 6** (`Section6.lean`): Lemma 6.1 (`H₂` moves past every letter,
  by Figure 8 and the definitions (1)–(20)), Lemma 6.2 and Theorem 6.3's
  argument (`H₂` is not dyadic), via the generic extension lemma of
  `LiRossSelinger/Extension.lean`: completeness and generation of `R₂` from
  those of `R₁`.
* Generation (surjectivity) of `O(8, 𝔻)` by `Σ₁` (`Encode.lean`): every
  generator of Li–Ross–Selinger's `𝒢₈` is the circuit of the paper's
  abbreviations (all 106 checked by the kernel), and Li–Ross–Selinger's
  Theorem 3.5 (proved in `LiRossSelinger/Generation.lean`).
* Completeness of `R₁` reduced to Li–Ross–Selinger's completeness at
  `n = 8` (`Translation.complete1_of`), given two families of derivations.

## Remaining `sorry`

* `Theorem.encodesTable1` (`EncodesTable1`): the encoding of each relation
  of Li–Ross–Selinger's Table 1 at `n = 8` is derivable from `R₁` — the
  Tietze `Rel(−)` steps of Sections 5.2–5.6, Appendix F and the supplement.
* `Theorem.roundTrip` (`RoundTrip`): each letter of `Σ₁` is derivably equal
  to the circuit of its decoding into level matrices (the `Gen(±)` steps).
* Through `LiRossSelinger.complete` (Li–Ross–Selinger's Theorem 4.10, its
  Main Lemma), which Theorem 5.2's completeness uses at `n = 8`.

Everything else (soundness, independence, Section 6, surjectivity) is
proved; Theorem 6.3 depends on the sorries only through completeness of
`R₁`.
