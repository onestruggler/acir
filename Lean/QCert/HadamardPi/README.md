# Hadamard-Π, §4.2: a presentation of Oₙ(ℤ[1/√2])

Fang, Heunen and Kaarsgaard, *Hadamard-Π: Equational quantum programming*,
POPL 2026, arXiv:2506.06835.  Formalized from the paper (TeX source and PDF)
in the QCert framework (`QCert.Presentation`, `QCert.Synthesis`,
`QCert.Matrix.Level`, `QCert.Matrix.Rings`).

## Main theorem

```lean
-- QCert/HadamardPi/Theorem.lean
theorem theorem_4_13 {n} {w w' : Word (Gen n)} (h : Derivable Fig6 w w') :
    FreeMonoid.lift (sem n) w = FreeMonoid.lift (sem n) w'
theorem theorem_4_14 (n : ℕ) : IsPresentationOf (Fig6 (n := n)) (sem n)
```

* `Gen n` is the generating set 𝒢ₙ of Definition 4.5: `(-1)_[a]`, `X_[b,c]` and
  `H_[b,c]` with `b < c`.  **Indices start at 0** (the paper's start at 1).
* `Fig6` is Figure 6: one constructor per relation scheme (a1)–(d4).  The
  caption says "the indices are distinct"; a scheme's instances are the
  assignments of distinct indices for which every generator it mentions is in
  𝒢ₙ (increasing indices).  Each constructor carries exactly those order
  conditions plus the remaining distinctness conditions.
* `sem n : Gen n → O_ZInvSqrt2 n` sends a generator to its one- or two-level
  matrix (`levelMat`), an element of Oₙ(ℤ[1/√2]) (Definitions 4.3, 4.4).

## Files

| File | Content | Paper |
|---|---|---|
| `Syntax.lean` | `Gen`, the notations `Z_[a]`, `X_[a,b]`, `H_[a,b]`, `Fig6` | Def. 4.5, Fig. 6 |
| `Semantics.lean` | generator matrices over any ring, `sem` | Defs. 4.3, 4.4, 4.12 |
| `Local.lean` | level matrices compose and multiply; exact checks over ℤ√2 with every generator scaled by √2, decided by `decide +kernel` and carried to ℝ | |
| `Soundness.lean` | every relation of Figure 6 (in dimension ≤ 6 at indices 0, 1, …, carried to any distinct indices); grouplike | Thm. 4.13 |
| `Arith.lean` | ℤ√2 ⊆ ℝ, denominator exponents, the parity facts | Defs. 4.1, 4.2; Lemma 4.6 (= Amy et al. 5.13) |
| `Column.lean` | least denominator exponents and numerators of unit vectors; exponent 0 gives ±e_a | Lemmas 4.6, 4.7 |
| `Actions.lean` | generators acting on columns; signed permutations keep exponents | |
| `Normal.lean` | pivots, levels (lexicographic), `H` on two odd entries of one class | Def. 4.9 |
| `Synth.lean` | syllables, **Theorem 4.10**, normal words, **generation** (`lift_sem_surjective`) | Alg. 1, Thm. 4.10, Thm. 4.8 |
| `Levels.lean` | how one generator changes the level | Lemma A.6 (levels) |
| `Derive.lean`, `Rel.lean` | rewriting derivations on lists (`rw_at`), the relations on lists, derived moves | |
| `Paths.lean` | closing squares along paths, `MainSquare` | Def. A.2–A.5 |
| `MainLemma.lean` | Lemma A.7 by Main Cases | Lemma A.7 |
| `Complete.lean` | Lemma A.6 (basic words and their levels), Lemma A.8, normal words as `QCert.NormalWords` | Lemmas A.6, A.8, A.9 |
| `Theorem.lean` | Theorems 4.13 and 4.14 | |

## What is proved

* Soundness (Theorem 4.13), every relation, no sorry.
* Grouplike (every generator is an involution).
* Generation (Theorem 4.8) and correctness of Algorithm 1 (Theorem 4.10), no
  sorry: `lift_sem_surjective`.
* The reduction of completeness to the Main Lemma (Lemmas A.6, A.8, A.9 and
  Theorem 4.14 through `QCert.NormalWords.isPresentationOf`), no sorry.
  Lemma A.6 is proved with its level bound (the path of the basic word stays
  below any bound on the levels of its two ends).
* The Main Lemma (Lemma A.7) for:
  * `G = (-1)_[0]`: Main Cases 5, 6, 7, 8, all subcases;
  * `G = X_[0,x]`: Main Cases 3 and 4 (exponent 0), and every case with `x` at
    or above the pivot (retrograde squares);
  * `G = H_[0,1]`: Main Cases 11 and 12 (exponent 0), and the case where the
    pivot is the first column (retrograde);
  * the base case `s = ⟦G⟧`.

## Remaining `sorry`s

Exactly two, both in `MainLemma.lean`; `theorem_4_14` depends on them
(`theorem_4_13` and `lift_sem_surjective` do not):

| Declaration | Stands for |
|---|---|
| `main_X_odd` | Main Cases 1 and 2 of Lemma A.7: `G = X_[1,x]` (ours `X_[0,x]`) with `x` below the pivot, at a positive exponent (`N = H_[1,i₂]` or `H_[1,i₂] X_[1,i₁]`) |
| `main_H_odd` | Main Cases 9 and 10 of Lemma A.7: `G = H_[1,2]` (ours `H_[0,1]`) with the pivot beyond the second column, at a positive exponent. Case 9 is where the paper's proof is wrong (below); Clément's Case 3.4 is the argument that closes it |

## Errors and gaps found in the paper

1. **Lemmas A.16 and A.17 are false.**  Both are stated for `M ∈ Oₙ(ℤ[1/√2])`
   with `level(M) = (j,k,4)`, `k ≥ 2`, the four odd entries in positions 1–4
   with residues `(1+√2, 1, 1+√2, 1)` (mod 2).  Counterexamples in dimension 6
   with `k = 4` (numerators `√2⁴ v`, a unit vector since
   `Σ(aᵢ² + 2bᵢ²) = 16` and `Σ aᵢbᵢ = 0`; any unit vector over ℤ[1/√2] is a
   column of some element of O₆(ℤ[1/√2])):
   * Lemma A.16: `√2⁴ v = (−1−√2, 1, −1−√2, 1, −2+√2, −√2)`.  Then
     `√2³ H₁₄H₂₃H₂₄H₂₃H₁₄ v` is in ℤ[√2]⁴ (the hypothesis) but
     `√2³ H₁₃H₂₄H₁₂H₁₃H₂₄ v` is not (the conclusion).
   * Lemma A.17: `√2⁴ v = (−1−√2, 1, −1−√2, −1, −2+√2, −√2)`.  Then
     `√2³ H₁₄H₂₃H₃₄H₂₃H₁₄ v` is in ℤ[√2]⁴ but `√2³ H₁₃H₂₄H₁₄H₁₃H₂₄ v` is not.

   Found and checked by an exhaustive search in exact arithmetic over ℚ(√2)
   (all unit vectors of dimension 6 with `k = 4` and entries of small norm;
   dimension ≤ 5 and `k ≤ 3` give none).  The proof of A.16 goes wrong in its
   second case (`a₃ + a₄` odd), where the norm equation is used to rule the case
   out.  Main Case 9 (`l = 4`, via Lemma A.19) rests on these two lemmas, so
   its proof is incomplete; QCert reports that the resulting case analysis also
   misses a case in dimension 9 (not re-derived here).  Clément's notes (row
   `QCert/Clement2019`) treat this situation as their Case 3.4.
2. **Main Case 1 (1) is wrong as stated.**  It claims that for `x < i₂` the
   first syllable of `X_[1,x] s` is `H_[1,i₂] X_[1,x]`.  This fails when an odd
   entry of the other class lies among the positions `2, …, x`.  Example
   (dimension 4, pivot column 4, `k = 3`):
   `√2³ v = (1, 1−√2, 1, 1+√2)` has `i₁ = 1`, `i₂ = 3`; with `x = 2`,
   `X_[1,2] v` has first syllable `H_[1,4]`, not `H_[1,3] X_[1,2]`.
3. **Main Cases 1 and 2 omit `x > j`.**  When `X_[1,x]` acts beyond the pivot,
   the first syllable of `X_[1,x] s` is `X_[1,x]` itself (the square is
   "retrograde"); formalized as `square_retro` with `syl_X_above`.
4. **Main Case 4 (3) for `x = j`.**  The case lists `x ≤ j` and cites (b2), (b3),
   but `X_[1,j]` and `X_[a,j]` share the index `j`; the square closes with
   `G' = X_[1,a]` instead, by (c3) (`main_X`, branch `x = j`).
5. Small citation slips: the first diagram of Lemma A.6 commutes by (c1), not
   (c4); the conjugations of Lemma A.6 for `H_[b,c]` need separate words when
   `b = 1` (ours `bw`, `bwH0`).

## Design notes

* Exact checks: an identity of words at symbolic indices is the image under
  `levelMat f` (`f` injective) of the identity at the indices `0, 1, …`, which
  is decided over `ℤ√2` with every generator scaled by `√2`
  (`wordMat_eq_of_check`); (d3) is checked in dimension 4 and (d4) in
  dimension 6.
* The level is `toLex (piv M, toLex (k, l))` with `piv M` one more than the
  index of the last column different from the basis vector.
* Derivations are chains of `rw_at w k h`: the segment of `w` at position `k`
  is rewritten by `h : L ≈ R`, checked by `rfl` on lists with symbolic
  indices.
