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
import QCert.LiRossSelinger.Semantics

namespace QCert.LiRossSelinger

/-- Theorems 3.5, 4.3 and 4.10: Table 1 presents `Oₙ(ℤ[1/2])`. -/
theorem presentation (n : ℕ) : IsPresentationOf (Table1 n) (sem n) := by
  sorry

/-- Theorems 5.4 and 5.7: for `n = m * 2 ≥ 2`, Tables 1 and 2 present `Lₙ`. -/
theorem presentationL (m : ℕ) (hm : 1 ≤ m) : IsPresentationOf (Table12 m) (semL m) := by
  sorry

end QCert.LiRossSelinger
