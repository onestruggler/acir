/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): the main theorems

* `theorem_5_2`: `R₁` — Figures 4 and 7 with the relation `(r_K)` of
  Section 5.5 restored — presents `O(8, 𝔻)` on `Σ₁` (Theorem 5.2,
  corrected).
* `rK_independent`, `theorem_5_2_as_stated_fails`: `(r_K)` does not follow
  from Figures 4 and 7, so these alone do not present `O(8, 𝔻)`.
* `theorem_6_3`: `R₂ = R₁ ∪` Figure 8 presents `TofH(3) = L₈` on `Σ₂`
  (Theorem 6.3).
-/
import QCert.ToffoliHadamard.Independence
import QCert.ToffoliHadamard.Section6

namespace QCert.ToffoliHadamard

/-- Completeness of `R₁` (to be proved through Li–Ross–Selinger). -/
theorem complete1 : ∀ ⦃u v : Word Sym1⦄,
    FreeMonoid.lift sem1 u = FreeMonoid.lift sem1 v → Derivable R1 u v := by
  sorry

/-- Every element of `O(8, 𝔻)` is the value of a word over `Σ₁`. -/
theorem surjective1 : Function.Surjective (FreeMonoid.lift sem1) := by
  sorry

/-- Theorem 5.2, corrected: Figures 4 and 7 and `(r_K)` present `O(8, 𝔻)`. -/
theorem theorem_5_2 : IsPresentationOf R1 sem1 where
  grouplike := grouplike1
  sound := sound1
  complete := complete1
  surjective := surjective1

/-- `(r_K)`, `K_{1,2} ≈ K_[4,5,6,7] X₀ K_[4,5,6,7] X₀`, is not derivable from
Figures 4 and 7. -/
theorem rK_independent : ¬ Derivable Fig47 (w [Sym1.K12]) (w rKrhs) := rK_independent'

/-- Theorem 5.2 as stated fails: Figures 4 and 7 alone do not present
`O(8, 𝔻)` (both sides of `(r_K)` have the same matrix). -/
theorem theorem_5_2_as_stated_fails : ¬ IsSubPresentationOf Fig47 sem1 :=
  fun h => rK_independent (h.complete (sound1 R1.rK))

/-- Completeness of `R₂`, from that of `R₁` (Lemmas 6.1, 6.2). -/
theorem complete2 : ∀ ⦃u v : Word Sym2⦄,
    FreeMonoid.lift sem2 u = FreeMonoid.lift sem2 v → Derivable R2 u v :=
  complete2_of complete1

/-- Every element of `TofH(3)` is the value of a word over `Σ₂`. -/
theorem surjective2 : Function.Surjective (FreeMonoid.lift sem2) :=
  surjective2_of surjective1

/-- Theorem 6.3: `R₂` presents `TofH(3)`. -/
theorem theorem_6_3 : IsPresentationOf R2 sem2 where
  grouplike := grouplike2
  sound := sound2
  complete := complete2
  surjective := surjective2

end QCert.ToffoliHadamard
