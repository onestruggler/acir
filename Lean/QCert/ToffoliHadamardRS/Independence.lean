/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: `r_K` is needed

Translation of `Independence.agda` (which the Agda's `gen/mk_indep.py`
writes; its clause tables are Lean case splits here).  The relation `r_K`
is not derivable from `R₁ = R₀ ∪ R₈₄`, so `R₁` alone is not complete for
`O(8, 𝔻)` (and the presentations here use `R₁⁺` and `R₂⁺`, which add it).

The model: each Toffoli-K gate `g` is read as `R g R`, where `R = I − J/4`
is the reflection in the vector of all ones (a circuit, `Rw`), and `NK` and
`CCZ` as themselves.  `R₀` holds, every relation of it being conjugated by
`R`; `R₈₄` holds, as its Toffoli-K gates are the permutations `X_j` and
`CCX`, which commute with `R`.  But `r_K` fails: `R K₁₂ R` is not `K₁₂`
(their entries at `(0, 0)` are `-1/4` and `1/2`), while the other side of
`r_K` is read as itself.
-/
import QCert.ToffoliHadamardRS.SoundnessH

namespace QCert.ToffoliHadamardRS

open Gate

/-! ## The model -/

/-- `I − J/4`, the reflection in the vector of all ones. -/
def Rw : Word G₁ := K01 * m0 * T 0 * m0 * K01

/-- Each Toffoli-K gate conjugated by `R`. -/
def σ : G₁ → Word G₁
  | .NK => NKw
  | .CCZ => CCZw
  | g => Rw * FreeMonoid.of g * Rw

abbrev σW : Word G₁ →* Word G₁ := FreeMonoid.lift σ

/-- The Toffoli-K gates, and the ones `R` commutes with. -/
def tkg : G₁ → Bool
  | .NK => false
  | .CCZ => false
  | _ => true

def fixg : G₁ → Bool
  | .X₀ | .X₁ | .X₂ | .CCX₀₁ | .CCX₀₂ | .CCX₁₂ | .NK | .CCZ => true
  | _ => false

def tk (w : Word G₁) : Bool := w.toList.all tkg
def fix (w : Word G₁) : Bool := w.toList.all fixg

/-- The model's reading of a circuit. -/
noncomputable def semM : Word G₁ →* O8 := semO.comp σW

noncomputable abbrev R : O8 := semO Rw

theorem RR : semO (Rw * Rw) = semO (1 : Word G₁) := semO_eq_of_check (by decide +kernel)

theorem R_mul_R : R * R = 1 := by rw [← map_mul, RR, map_one]

theorem fix_X₀ : semO (Rw * X0 * Rw) = semO (X0 : Word G₁) := semO_eq_of_check (by decide +kernel)
theorem fix_X₁ : semO (Rw * X1 * Rw) = semO (X1 : Word G₁) := semO_eq_of_check (by decide +kernel)
theorem fix_X₂ : semO (Rw * X2 * Rw) = semO (X2 : Word G₁) := semO_eq_of_check (by decide +kernel)
theorem fix_CCX₀₁ : semO (Rw * CCX01 * Rw) = semO (CCX01 : Word G₁) := semO_eq_of_check (by decide +kernel)
theorem fix_CCX₀₂ : semO (Rw * CCX02 * Rw) = semO (CCX02 : Word G₁) := semO_eq_of_check (by decide +kernel)
theorem fix_CCX₁₂ : semO (Rw * CCX12 * Rw) = semO (CCX12 : Word G₁) := semO_eq_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `r_K` fails: the entries at `(0, 0)` differ. -/
theorem separates : semM K12 ≠ semM (X0 * NKw * X0 * NKw) := by
  simp only [semM, MonoidHom.comp_apply]
  exact semO_ne_of_entry 0 0 (by decide +kernel)

/-- On Toffoli-K circuits the model is conjugation by `R`. -/
theorem twist (w : Word G₁) (h : tk w = true) : semM w = R * semO w * R := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [map_one, R_mul_R]
  | mul_of g w ih =>
    simp only [tk, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      List.all_cons, Bool.and_eq_true] at h
    have hg : semM (FreeMonoid.of g) = R * semO (FreeMonoid.of g) * R := by
      cases g <;> simp [tkg] at h <;>
        simp only [semM, MonoidHom.comp_apply, FreeMonoid.lift_eval_of, σ, map_mul]
    rw [map_mul, hg, ih h.2, map_mul]
    calc R * semO (FreeMonoid.of g) * R * (R * semO w * R)
        = R * semO (FreeMonoid.of g) * (R * R) * semO w * R := by simp only [mul_assoc]
      _ = R * (semO (FreeMonoid.of g) * semO w) * R := by rw [R_mul_R]; simp only [mul_one, mul_assoc]

/-- On circuits of permutations `X_j`, `CCX`, and of `NK` and `CCZ`, the
model is the semantics. -/
theorem fixed (w : Word G₁) (h : fix w = true) : semM w = semO w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    simp only [fix, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
      List.all_cons, Bool.and_eq_true] at h
    have hg : semM (FreeMonoid.of g) = semO (FreeMonoid.of g) := by
      cases g <;> simp [fixg] at h <;>
        simp only [semM, MonoidHom.comp_apply, FreeMonoid.lift_eval_of, σ]
      · exact fix_X₀
      · exact fix_X₁
      · exact fix_X₂
      · exact fix_CCX₀₁
      · exact fix_CCX₀₂
      · exact fix_CCX₁₂
    rw [map_mul, hg, ih h.2, map_mul]

/-! ## `R₁` holds in the model -/

theorem sound_ax {w v : Word G₁} : R1 w v → semM w = semM v
  | .fig4 r => by
    have e := sound0 (by norm_num) r
    have ⟨hw, hv⟩ : tk w = true ∧ tk v = true := by cases r <;> exact ⟨by decide, by decide⟩
    rw [twist w hw, twist v hv, e]
  | .fig7 r => by
    have e := sound7 (k := 0) (by norm_num) r
    have ⟨hw, hv⟩ : fix w = true ∧ fix v = true := by
      cases r <;> exact ⟨by decide +kernel, by decide +kernel⟩
    rw [fixed w hw, fixed v hv, e]

theorem sound' {w v : Word G₁} (d : Derivable R1 w v) : semM w = semM v :=
  derivable_hom semM (fun _ _ r => sound_ax r) d

/-! ## `r_K` is independent of `R₁` -/

theorem rK_independent : ¬ Derivable R1 K12 (X0 * NKw * X0 * NKw) :=
  fun e => separates (sound' e)

/-- So `R₁` is not complete for `O(8, 𝔻)`: `r_K` holds of the matrices. -/
theorem R1_incomplete : semO (K12 : Word G₁) = semO (X0 * NKw * X0 * NKw : Word G₁) ∧
    ¬ Derivable R1 K12 (X0 * NKw * X0 * NKw) :=
  ⟨soundK (k := 0) (by norm_num) RK.rK, rK_independent⟩

end QCert.ToffoliHadamardRS
