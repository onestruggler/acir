/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: soundness in `L₈`

Translation of `SoundnessH.agda`.  Soundness in `TofH(3) = L₈`.  A circuit
without `H₂` denotes there the image of its value in `O(8, 𝔻)`
(`semH_noH`), so Figures 4 and 7 and `r_K` hold by `Soundness`; the
relations of Figure 8 are checked by computing their values.  Then the
congruences `R₁`, `R₁⁺` (in `O(8, 𝔻)`) and `R₂`, `R₂⁺` (in `L₈`) are sound.
-/
import QCert.ToffoliHadamardRS.Soundness
import QCert.ToffoliHadamardRS.Congruence
import QCert.LiRossSelinger.PushL

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (Gen GenL toL semL_toL_eq)

variable {k : ℕ}

/-! ## Circuits without `H₂` -/

/-- A letter other than `H₂`. -/
def noHg : Gate k → Bool
  | .H₂ => false
  | _ => true

/-- A circuit without `H₂`. -/
def noH (w : Word (Gate k)) : Bool := w.toList.all noHg

theorem encL_noH (g : Gate k) (h : noHg g = true) : encL g = toL (enc g) := by
  cases g <;> first | rfl | simp [noHg] at h

/-- An `H₂`-free circuit is encoded as a word over `𝒢₈`. -/
theorem encLW_noH (w : Word (Gate k)) (h : noH w = true) : encLW w = toL (encW w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    simp only [noH, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      List.all_cons, Bool.and_eq_true] at h
    rw [map_mul, map_mul, map_mul, ih h.2, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of,
      encL_noH g h.1]

/-- Its value in `L₈` is that in `O(8, 𝔻)`. -/
theorem semH_noH (w : Word (Gate k)) (h : noH w = true) :
    ((semH w : TofH3) : Matrix.unitaryGroup (Fin 8) ℝ) = ((semO w : O8) : Matrix.unitaryGroup (Fin 8) ℝ) := by
  show ((FreeMonoid.lift (LiRossSelinger.semL 4) (encLW w) : LiRossSelinger.L (4 * 2)) :
    Matrix.unitaryGroup (Fin (4 * 2)) ℝ) = _
  rw [encLW_noH w h]; exact semL_toL_eq (m := 4) (encW w)

theorem transfer {w v : Word (Gate k)} (hw : noH w = true) (hv : noH v = true)
    (e : semO w = semO v) : semH w = semH v :=
  Subtype.ext (by rw [semH_noH w hw, semH_noH v hv, e])

/-! ## Figures 4 and 7 and `r_K` at level 2 -/

theorem soundH0 {w v : Word G₂} (h : R0 w v) : semH w = semH v := by
  have e := sound0 (by norm_num) h
  cases h <;> exact transfer (by decide +kernel) (by decide +kernel) e

theorem soundH7 {w v : Word G₂} (h : Fig7 w v) : semH w = semH v := by
  have e := sound7 (k := 1) (by norm_num) h
  cases h <;> exact transfer (by decide +kernel) (by decide +kernel) e

theorem soundHK {w v : Word G₂} (h : RK w v) : semH w = semH v := by
  have e := soundK (k := 1) (by norm_num) h
  cases h; exact transfer (by decide +kernel) (by decide +kernel) e

/-! ## Figure 8, computed -/

theorem sound8 {w v : Word G₂} (h : Fig8 w v) : semH w = semH v := by
  cases h <;> exact semH_eq_of_check (by decide +kernel)

/-! ## The congruences -/

/-- `R₁⁺` in `O(8, 𝔻)`. -/
theorem sound1plus_ax {w v : Word G₁} : R1plus w v → semO w = semO v
  | .fig4 r => sound0 (by norm_num) r
  | .fig7 r => sound7 (k := 0) (by norm_num) r
  | .rK r => soundK (k := 0) (by norm_num) r

theorem sound1_ax {w v : Word G₁} : R1 w v → semO w = semO v
  | .fig4 r => sound0 (by norm_num) r
  | .fig7 r => sound7 (k := 0) (by norm_num) r

/-- `R₀` (at level 0), `R₁` and `R₁⁺` are sound in `O(8, 𝔻)`. -/
theorem sound0_der {w v : Word GD} (d : Derivable (R0 (k := 0)) w v) : semO w = semO v :=
  derivable_hom semO (fun _ _ r => sound0 (by norm_num) r) d

theorem sound1_der {w v : Word G₁} (d : Derivable R1 w v) : semO w = semO v :=
  derivable_hom semO (fun _ _ r => sound1_ax r) d

theorem sound1plus_der {w v : Word G₁} (d : Derivable R1plus w v) : semO w = semO v :=
  derivable_hom semO (fun _ _ r => sound1plus_ax r) d

/-- `R₂` and `R₂⁺` are sound in `L₈`. -/
theorem sound2_ax {w v : Word G₂} : R2 w v → semH w = semH v
  | .fig4 r => soundH0 r
  | .fig7 r => soundH7 r
  | .fig8 r => sound8 r

theorem sound2plus_ax {w v : Word G₂} : R2plus w v → semH w = semH v
  | .fig4 r => soundH0 r
  | .fig7 r => soundH7 r
  | .fig8 r => sound8 r
  | .rK r => soundHK r

theorem sound2_der {w v : Word G₂} (d : Derivable R2 w v) : semH w = semH v :=
  derivable_hom semH (fun _ _ r => sound2_ax r) d

theorem sound2plus_der {w v : Word G₂} (d : Derivable R2plus w v) : semH w = semH v :=
  derivable_hom semH (fun _ _ r => sound2plus_ax r) d

end QCert.ToffoliHadamardRS
