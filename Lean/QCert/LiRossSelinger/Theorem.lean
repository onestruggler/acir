/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): the main theorems

* `presentation`: the relations of Table 1 present `Oₙ(ℤ[1/2])` on the
  generators `𝒢ₙ`, in every dimension `n` (Theorem 3.5, generation;
  Theorem 4.3, soundness; Theorem 4.10, completeness).
* `presentationL`: for even `n = 2m ≥ 2`, the relations of Tables 1 and 2
  present `Lₙ` on `𝓕ₙ = 𝒢ₙ ∪ {I ⊗ H}` (Theorems 5.4 and 5.7; generation as
  in Section 5).
-/
import QCert.LiRossSelinger.PushL
import QCert.LiRossSelinger.Generation
import QCert.LiRossSelinger.Decomp

namespace QCert.LiRossSelinger

/-- Lemma A.20, the Main Lemma for the basic edges that do not raise the level. -/
theorem mainLemmaBasic (n : ℕ) : MainLemmaBasic n := by
  sorry

/-- Lemma A.19 (cited from Greylyn 2014 in the paper), with the level bound
at every intermediate state (`Decomp.lemmaA19`). -/
theorem basicDecomp (n : ℕ) : BasicDecomp n := lemmaA19

/-- Theorem 4.10 (completeness), by induction on the level of edges
(`Reduction.complete_of`). -/
theorem complete (n : ℕ) : ∀ ⦃u v : Word (Gen n)⦄,
    FreeMonoid.lift (sem n) u = FreeMonoid.lift (sem n) v → Derivable (Table1 n) u v :=
  complete_of (mainLemmaBasic n) (basicDecomp n)

/-- Theorem 3.5 (generation): every element of `Oₙ(ℤ[1/2])` is a product of
generators. -/
theorem surjective (n : ℕ) : Function.Surjective (FreeMonoid.lift (sem n)) := generation

/-- Theorems 3.5, 4.3 and 4.10: Table 1 presents `Oₙ(ℤ[1/2])`. -/
theorem presentation (n : ℕ) : IsPresentationOf (Table1 n) (sem n) where
  grouplike := grouplike
  sound := sound
  complete := complete n
  surjective := surjective n

/-- Theorem 5.7 (completeness), from Theorem 4.10 by Lemma 5.5 and
Corollary 5.6. -/
theorem completeL (m : ℕ) (hm : 1 ≤ m) : ∀ ⦃u v : Word (GenL m)⦄,
    FreeMonoid.lift (semL m) u = FreeMonoid.lift (semL m) v → Derivable (Table12 m) u v :=
  completeL_of hm (complete (m * 2))

/-- Generation of `Lₙ` by `𝓕ₙ` (Section 5), from Theorem 3.5. -/
theorem surjectiveL (m : ℕ) : Function.Surjective (FreeMonoid.lift (semL m)) :=
  surjectiveL_of (surjective (m * 2))

/-- Theorems 5.4 and 5.7: for `n = m * 2 ≥ 2`, Tables 1 and 2 present `Lₙ`. -/
theorem presentationL (m : ℕ) (hm : 1 ≤ m) : IsPresentationOf (Table12 m) (semL m) where
  grouplike := grouplikeL
  sound := soundL
  complete := completeL m hm
  surjective := surjectiveL m

end QCert.LiRossSelinger
