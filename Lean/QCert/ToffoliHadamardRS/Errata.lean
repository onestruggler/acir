/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: the errata

Translation of `Errata.agda`: the errata of the Agda development's
`ERRATA.md`, checked on the values: each printed equation that is false is
refuted by one entry of its two sides (`semO_ne_of_entry`), and each
correction that the rest of the development does not already check is
checked by computing both sides.

The corrections to (33), (97) and (100) are the relations `r33`, `r97` and
`r100` of `Syntactics`, and `Soundness` checks them; the corrected alias
`(-1)_[0]` is `StdMatrices.mm0`, and `X_[6,7] = CCX₀₁` is `StdMatrices.mT6`.
That `r_K` does not follow from `R₁` is `Independence.R1_incomplete`.
-/
import QCert.ToffoliHadamardRS.Decide
import QCert.ToffoliHadamardRS.Syntactics

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (sem)

/-- The value at level 0. -/
noncomputable abbrev sem₀ (w : Word GD) : O8 := semO w

/-- The value at level 1. -/
noncomputable abbrev semₗ₁ (w : Word G₁) : O8 := semO w

/-! ## The printed equations are false -/

/-- (33), Figure 4: `CCX₀₁ ≈ σ₁₂ CCX₀₂ σ₀₂` is false (entry `(1, 1)`: `1`
against `0`). -/
theorem r033_false : sem₀ CCX01 ≠ sem₀ (SW12 * CCX02 * SW02) :=
  semO_ne_of_entry 1 1 (by decide +kernel)

/-- Section 5.5: `CCX₁₂ = X_[6,7]` is false (entry `(3, 3)`); `CCX₁₂` is
`X_[3,7]`. -/
theorem x67_false : sem₀ CCX12 ≠ FreeMonoid.lift (sem 8) (Xw 6 7) :=
  semO_ne_sem8_of_entry 3 3 (by decide +kernel)

theorem ccx12 : sem₀ CCX12 = FreeMonoid.lift (sem 8) (Xw 3 7) :=
  semO_eq_sem8_of_check (by decide +kernel)

/-- Section 5.5, `(r_CX)`: `CX₀₁ ≈ X_[2,6] X_[3,7]` is false (entry
`(2, 2)`); `X_[2,6] X_[3,7]` is `CX₁₀`, and `CX₀₁` is `X_[4,6] X_[5,7]`. -/
theorem rCX_false : sem₀ CX01 ≠ FreeMonoid.lift (sem 8) (Xw 2 6 * Xw 3 7) :=
  semO_ne_sem8_of_entry 2 2 (by decide +kernel)

theorem cx10 : sem₀ CX10 = FreeMonoid.lift (sem 8) (Xw 2 6 * Xw 3 7) :=
  semO_eq_sem8_of_check (by decide +kernel)

theorem rCX : sem₀ CX01 = FreeMonoid.lift (sem 8) (Xw 4 6 * Xw 5 7) :=
  semO_eq_sem8_of_check (by decide +kernel)

/-- Section 5.6: `(-1)_[0] = X₀ X₁ CCZ X₁ X₀` is false (entry `(0, 0)`); the
right-hand side is `(-1)_[1]`. -/
theorem m0_false : FreeMonoid.lift (sem 8) (Mw 0) ≠ semₗ₁ (X0 * X1 * CCZw * X1 * X0) :=
  (semO_ne_sem8_of_entry 0 0 (by decide +kernel)).symm

theorem m1 : semₗ₁ (X0 * X1 * CCZw * X1 * X0) = FreeMonoid.lift (sem 8) (Mw 1) :=
  semO_eq_sem8_of_check (by decide +kernel)

/-- (97), Figure 7: `X_[0,1] K_[0,1,2,3] ≈ K_[0,1,2,3] X_[0,1] (-1)_[1]
(-1)_[3]` is false (entry `(1, 1)`: `1/2` against `-1/2`). -/
theorem r097_false : semₗ₁ (T 0 * NKw) ≠ semₗ₁ (NKw * T 0 * m 1 * m 3) :=
  semO_ne_of_entry 1 1 (by decide +kernel)

/-- (100), Figure 7: `K_[0,1,2,3]` and `K_[1,3,4,5]` do not commute. -/
theorem r100_false : semₗ₁ (NKw * Kq 1 3 4 5) ≠ semₗ₁ (Kq 1 3 4 5 * NKw) :=
  semO_ne_of_entry 0 3 (by decide +kernel)

/-- Section 5.7: `CCZ = K₁₂ CZ₁₂ X₀ K_[0,1,2,3] X₀ CZ₁₂ K_[0,1,2,3] X_[5,6]`
is false (entry `(4, 4)`: `1` against `1/2`); with `K₁₂` for the second
`K_[0,1,2,3]` it holds. -/
theorem ccz_false : semₗ₁ CCZw ≠ semₗ₁ (K12 * CZ12 * X0 * NKw * X0 * CZ12 * NKw * T 5) :=
  semO_ne_of_entry 4 4 (by decide +kernel)

theorem ccz : semₗ₁ CCZw = semₗ₁ (K12 * CZ12 * X0 * NKw * X0 * CZ12 * K12 * T 5) :=
  semO_eq_of_check (by decide +kernel)

/-- The other decomposition of Section 5.7 holds as printed. -/
theorem nk : semₗ₁ NKw = semₗ₁ ((K12 * CCZw) * (K12 * CCZw) * (K12 * CCZw) * T 5) :=
  semO_eq_of_check (by decide +kernel)

end QCert.ToffoliHadamardRS
