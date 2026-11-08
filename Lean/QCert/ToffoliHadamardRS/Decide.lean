/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: deciding values

The Lean counterpart of `Decide.agda`, where the equality of two computed
matrices is decided by one Boolean.  Here the Boolean is Li–Ross–Selinger's
`ListMat.eqS` on scaled integer matrices: every generator of `𝒢₈` is
`(1/√2)^s` times an integer row operation (a permutation, row signs, or a
dense matrix; `gAct`, `gSc`), and so is `I ⊗ H` (`lAct`, `lSc`), so the
matrix of a word is a scaled integer matrix computed by the kernel
(`ListMat.evalSM`), and an equation of words decided there holds in
`O(8, 𝔻)` (`semO_eq_of_check`) and in `L₈` (`semH_eq_of_check`).

The row operation of each generator is checked against its level matrix once
per generator (`bridge_gen`, Li–Ross–Selinger's `Loc.bridge` over `ℚ`), not
once per occurrence.
-/
import QCert.ToffoliHadamardRS.Semantics
import QCert.LiRossSelinger.Local
import QCert.LiRossSelinger.Blocks

namespace QCert.ToffoliHadamardRS

open Matrix QCert.ListMat LiRossSelinger
open scoped Kronecker

noncomputable section

/-! ## Generators of `𝒢₈` as row operations -/

/-- A generator of `𝒢ₙ` on its own indices. -/
def toLoc {n : ℕ} : Gen n → Loc
  | .neg a => .neg a.val
  | .x a b _ => .x a.val b.val
  | .k a b c d _ _ _ => .k a.val b.val c.val d.val

theorem bridge_neg : ∀ a : Fin 8, Loc.bridge 8 (.neg a.val) = true := by decide +kernel

theorem bridge_x : ∀ a b : Fin 8, a < b → Loc.bridge 8 (.x a.val b.val) = true := by
  decide +kernel

theorem bridge_k : ∀ a b c d : Fin 8, a < b → b < c → c < d →
    Loc.bridge 8 (.k a.val b.val c.val d.val) = true := by
  decide +kernel

theorem bridge_gen : ∀ g : Gen 8, Loc.bridge 8 (toLoc g) = true
  | .neg a => bridge_neg a
  | .x a b h => bridge_x a b h
  | .k a b c d h₁ h₂ h₃ => bridge_k a b c d h₁ h₂ h₃

theorem levelMat_id {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : levelMat (id : Fin n → Fin n) M = M := by
  ext i j; exact levelMat_apply_apply (f := id) Function.injective_id M i j

theorem genMat_glob (g : Gen 8) : genMat g = (toLoc g).glob id := by
  cases g with
  | neg a => exact genMat_neg_loc id a.val a.isLt a rfl
  | x a b h =>
    exact genMat_x_loc id a.val b.val a.isLt b.isLt (Fin.val_ne_of_ne (ne_of_lt h)) a b h rfl rfl
  | k a b c d h₁ h₂ h₃ =>
    have hd : [a.val, b.val, c.val, d.val].Nodup := by
      have e₁ : a.val < b.val := h₁
      have e₂ : b.val < c.val := h₂
      have e₃ : c.val < d.val := h₃
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      omega
    exact genMat_k_loc id a.val b.val c.val d.val a.isLt b.isLt c.isLt d.isLt hd a b c d h₁ h₂ h₃
      rfl rfl rfl rfl

/-- The power of `1/√2` a generator carries. -/
def gSc (g : Gen 8) : ℕ := 2 * (toLoc g).sc

/-- The integer row operation of a generator. -/
def gAct (g : Gen 8) : Act ℤ := Loc.act 8 (toLoc g)

theorem gAct_wf (g : Gen 8) : (gAct g).WF 8 := (Loc.bridge_spec (bridge_gen g)).1

theorem half_eq_isqrt2_sq (s : ℕ) : (1 / 2 : ℝ) ^ s = (Real.sqrt 2)⁻¹ ^ (2 * s) := by
  rw [pow_mul, inv_pow, Real.sq_sqrt (by norm_num), one_div]

theorem genMat_act (g : Gen 8) :
    genMat g = (Real.sqrt 2)⁻¹ ^ gSc g • ((gAct g).toMat 8).map (Int.castRingHom ℝ) := by
  rw [genMat_glob, Loc.glob, (Loc.bridge_spec (bridge_gen g)).2, levelMat_id, gSc,
    half_eq_isqrt2_sq]; rfl

/-! ## `I ⊗ H` as a row operation -/

/-- `√2 (I ⊗ H)` on eight indices. -/
def lIH : LMat ℤ := [[1, 1, 0, 0, 0, 0, 0, 0], [1, -1, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 1, -1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0],
  [0, 0, 0, 0, 1, -1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1, -1]]

/-- `√2 (I ⊗ H)` as a Kronecker product. -/
def nIH : Matrix (Fin (4 * 2)) (Fin (4 * 2)) ℤ :=
  ((1 : Matrix (Fin 4) (Fin 4) ℤ) ⊗ₖ !![1, 1; 1, -1]).submatrix finProdFinEquiv.symm
    finProdFinEquiv.symm

theorem nIH_eq : nIH = ListMat.toMat 8 lIH := by decide +kernel

theorem matIH_eq : matIH 4 = (Real.sqrt 2)⁻¹ ^ 1 • (ListMat.toMat 8 lIH).map (Int.castRingHom ℝ) := by
  rw [← nIH_eq, pow_one]
  ext i j
  simp only [matIH, nIH, submatrix_apply, smul_apply, map_apply, smul_eq_mul]
  generalize finProdFinEquiv.symm i = x
  generalize finProdFinEquiv.symm j = y
  obtain ⟨a, p⟩ := x
  obtain ⟨b, q⟩ := y
  simp only [kronecker_apply, one_apply]
  split_ifs <;> fin_cases p <;> fin_cases q <;> simp [matH]

/-! ## The generators of `𝓕₈` -/

/-- The scale of a generator of `𝓕₈`. -/
def lSc : GenL 4 → ℕ
  | .base g => gSc g
  | .ih => 1

/-- The row operation of a generator of `𝓕₈`. -/
def lAct : GenL 4 → Act ℤ
  | .base g => gAct g
  | .ih => .dense lIH

theorem lAct_wf : ∀ x : GenL 4, (lAct x).WF 8
  | .base g => gAct_wf g
  | .ih => by decide

/-- The matrix of a generator of `𝓕₈`. -/
def lMat (x : GenL 4) : Matrix (Fin 8) (Fin 8) ℝ :=
  (((semL 4 x : L (4 * 2)) : unitaryGroup (Fin (4 * 2)) ℝ) : Matrix (Fin 8) (Fin 8) ℝ)

theorem lMat_act : ∀ x : GenL 4,
    lMat x = (Real.sqrt 2)⁻¹ ^ lSc x • ((lAct x).toMat 8).map (Int.castRingHom ℝ)
  | .base g => genMat_act g
  | .ih => matIH_eq

/-! ## Words -/

/-- The matrix of the value of a word in a subgroup of the orthogonal group. -/
theorem coe_lift {X : Type*} {S : Subgroup (unitaryGroup (Fin 8) ℝ)} (f : X → S) (u : Word X) :
    (((FreeMonoid.lift f u : S) : unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ) =
      (u.toList.map fun x => (((f x : S) : unitaryGroup (Fin 8) ℝ) : Matrix (Fin 8) (Fin 8) ℝ)).prod := by
  induction u using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g u ih =>
    rw [map_mul, Subgroup.coe_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append, List.map_cons,
      List.prod_cons]

theorem two_isqrt2_sq : (2 : ℝ) * (Real.sqrt 2)⁻¹ ^ 2 = 1 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- An identity of words of row operations decided on scaled integer
matrices holds for their real matrices. -/
theorem prod_eq_of_eqS {X : Type*} (F : X → Matrix (Fin 8) (Fin 8) ℝ) (sc : X → ℕ)
    (act : X → Act ℤ) (hwf : ∀ x, (act x).WF 8)
    (hF : ∀ x, F x = (Real.sqrt 2)⁻¹ ^ sc x • ((act x).toMat 8).map (Int.castRingHom ℝ))
    {l l' : List X} (h : eqS 2 (evalSM 8 sc act l) (evalSM 8 sc act l') = true) :
    (l.map F).prod = (l'.map F).prod := by
  rw [toMatS_evalSM 8 _ sc act F l (fun x _ => hwf x) (fun x _ => hF x),
    toMatS_evalSM 8 _ sc act F l' (fun x _ => hwf x) (fun x _ => hF x)]
  exact eqS_sound 8 two_isqrt2_sq h

/-- The scaled integer matrix of a word over `𝒢₈`. -/
def evalG (l : List (Gen 8)) : SMat := evalSM 8 gSc gAct l

/-- The scaled integer matrix of a word over `𝓕₈`. -/
def evalL (l : List (GenL 4)) : SMat := evalSM 8 lSc lAct l

theorem sem8_eq_of_check {u v : Word (Gen 8)} (h : eqS 2 (evalG u.toList) (evalG v.toList) = true) :
    FreeMonoid.lift (sem 8) u = FreeMonoid.lift (sem 8) v := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_lift, coe_lift]
  exact prod_eq_of_eqS genMat gSc gAct gAct_wf genMat_act h

theorem semL_eq_of_check {u v : Word (GenL 4)} (h : eqS 2 (evalL u.toList) (evalL v.toList) = true) :
    FreeMonoid.lift (semL 4) u = FreeMonoid.lift (semL 4) v := by
  apply Subtype.ext; apply Subtype.ext
  rw [coe_lift, coe_lift]
  exact prod_eq_of_eqS lMat lSc lAct lAct_wf lMat_act h

end

/-! ## Circuits -/

/-- Two circuits have the same value in `O(8, 𝔻)`, decided. -/
def checkO {k : ℕ} (w v : List (Gate k)) : Bool := eqS 2 (evalG (encList w)) (evalG (encList v))

/-- Two circuits have the same value in `L₈`, decided. -/
def checkH {k : ℕ} (w v : List (Gate k)) : Bool := eqS 2 (evalL (encLList w)) (evalL (encLList v))

theorem semO_eq_of_check {k : ℕ} {w v : Word (Gate k)} (h : checkO w.toList v.toList = true) :
    semO w = semO v := by
  show FreeMonoid.lift (sem 8) (encW w) = FreeMonoid.lift (sem 8) (encW v)
  apply sem8_eq_of_check
  rw [encW_toList, encW_toList]; exact h

theorem semH_eq_of_check {k : ℕ} {w v : Word (Gate k)} (h : checkH w.toList v.toList = true) :
    semH w = semH v := by
  show FreeMonoid.lift (semL 4) (encLW w) = FreeMonoid.lift (semL 4) (encLW v)
  apply semL_eq_of_check
  rw [encLW_toList, encLW_toList]; exact h

end QCert.ToffoliHadamardRS
