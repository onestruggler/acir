/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: decoding `𝓕₈`

Translation of `DecodeH.agda`.  The generators `𝓕₈` of Li, Ross and
Selinger's §5 decoded as circuits over `Σ₂`: a generator of `𝒢₈` as in
`Decode`, and `I ⊗ H` as `H₂`.  The decoding respects Tables 1 and 2:
Table 1 by `Decode` one level up, and each relation `H g H = t` of Table 2
by passing `H₂` through the decoding of `g` (`Push`) and comparing values,
`R₁⁺` being complete.
-/
import QCert.ToffoliHadamardRS.TableMatrices
import Mathlib.Tactic.IntervalCases

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (Gen GenL Table12 toL)

/-! ## The decoding -/

/-- The decoding of a generator of `𝓕₈`. -/
def decL : GenL 4 → Word G₂
  | .base g => upW (dec g)
  | .ih => H2

abbrev decLW : Word (GenL 4) →* Word G₂ := FreeMonoid.lift decL

theorem decL_toL (w : Word (Gen (4 * 2))) : decLW (toL w) = upW (decW w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, map_mul, ih, FreeMonoid.map_of, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of]; rfl

/-! ## Table 2 -/

/-- `H₂` around a circuit over `Σ₁` that it turns into `t`. -/
theorem conj_H (w t : Word G₁) (m : sem₁ (conjW w) = sem₁ t) :
    Derivable R2plus (H2 * upW w * H2) (upW t) := by
  have p := (pushW w).mul (Derivable.refl H2)
  rw [mul_assoc (upW (conjW w))] at p
  refine p.trans ?_
  have e := (Derivable.refl (upW (conjW w))).mul (Derivable.of (R2plus.fig8 (Fig8.r108 (k := 0))))
  rw [mul_one] at e
  exact e.trans (lift12 (complete1 m))

theorem conj_case {u v : Word (GenL 4)} (w t : Word G₁) (m : sem₁ (conjW w) = sem₁ t)
    (e₁ : decLW u = H2 * upW w * H2) (e₂ : decLW v = upW t) : Derivable R2plus (decLW u) (decLW v) :=
  e₁ ▸ e₂ ▸ conj_H w t m

/-- The decoding respects the relations of Tables 1 and 2. -/
theorem decL_ax {u v : Word (GenL 4)} (h : Table12 4 u v) : Derivable R2plus (decLW u) (decLW v) := by
  cases h with
  | table1 r =>
    rw [decL_toL, decL_toL]; exact lift12 (dec_cong Toffoli.coxeter1 (Derivable.of r))
  | r7a =>
    simp only [map_mul, map_one, FreeMonoid.lift_eval_of, LiRossSelinger.IH, decL]
    exact Derivable.of (R2plus.fig8 Fig8.r108)
  | r7b h =>
    exact conj_case K0123 K0123 t7b
      (by simp [LiRossSelinger.IH, decL]; rfl) (by simp [decL]; rfl)
  | r7c h =>
    exact conj_case M0 (M0 * X01 * M0) t7c
      (by simp [LiRossSelinger.IH, decL]; rfl) (by simp [decL]; rfl)
  | r7d_even a ha h =>
    have : a < 7 := by omega
    interval_cases a <;> simp at ha
    · exact conj_case X01 M1 t7d0 (by simp [LiRossSelinger.IH, decL]; rfl) (by simp [decL]; rfl)
    · exact conj_case X23 M3 t7d2 (by simp [LiRossSelinger.IH, decL]; rfl) (by simp [decL]; rfl)
    · exact conj_case X45 M5 t7d4 (by simp [LiRossSelinger.IH, decL]; rfl) (by simp [decL]; rfl)
    · exact conj_case X67 M7 t7d6 (by simp [LiRossSelinger.IH, decL]; rfl) (by simp [decL]; rfl)
  | r7d_odd a ha h =>
    have : a < 6 := by omega
    interval_cases a <;> simp at ha
    · exact conj_case X12 (X12 * K0123) t7d1 (by simp [LiRossSelinger.IH, decL]; rfl)
        (by simp [decL]; rfl)
    · exact conj_case X34 (X34 * K2345) t7d3 (by simp [LiRossSelinger.IH, decL]; rfl)
        (by simp [decL]; rfl)
    · exact conj_case X56 (X56 * K4567) t7d5 (by simp [LiRossSelinger.IH, decL]; rfl)
        (by simp [decL]; rfl)

theorem decL_cong {u v : Word (GenL 4)} (h : Derivable (Table12 4) u v) :
    Derivable R2plus (decLW u) (decLW v) :=
  derivable_map decLW (fun _ _ r => decL_ax r) h

end QCert.ToffoliHadamardRS
