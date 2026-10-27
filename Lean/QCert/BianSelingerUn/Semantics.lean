/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Bian–Selinger: the matrices of the generators

The generators of §3.1 read as one- and two-level matrices (Definition 2.6)
of the types `X = [[0,1],[1,0]]`, `K = ω† H = (1/(1+i)) [[1,1],[1,-1]]`
(§1) and `i`, as elements of the target group `Uₙ(ℤ[1/2, i])` (`U_ZHalfI`).
-/
import QCert.BianSelingerUn.Syntax
import QCert.BianSelingerUn.LevelCalc

namespace QCert.BianSelingerUn

open Matrix Complex

noncomputable section

/-- The matrix `X`. -/
def Xmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The matrix `K = ω† H = (1/(1+i)) [[1, 1], [1, -1]]`. -/
def Kmat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + I)⁻¹, (1 + I)⁻¹; (1 + I)⁻¹, -(1 + I)⁻¹]

theorem inv_one_add_I : (1 + I)⁻¹ = (1 - I) / 2 := by
  apply inv_eq_of_mul_eq_one_right
  ring_nf
  rw [I_sq]
  ring

theorem Xmat_mem_unitaryGroup : Xmat ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Xmat, mul_apply, Fin.sum_univ_two]

theorem Kmat_mem_unitaryGroup : Kmat ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff]
  have h : (1 + I)⁻¹ * (1 + -I)⁻¹ = 1 / 2 := by
    rw [← mul_inv, one_div]
    congr 1
    ring_nf; rw [I_sq]; ring
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Kmat, mul_apply, Fin.sum_univ_two]
  all_goals rw [h]; norm_num

theorem I_mem_unitaryGroup : !![I] ∈ unitaryGroup (Fin 1) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext a b
  fin_cases a; fin_cases b
  simp [mul_apply]

variable {n : ℕ}

/-- The matrix of a generator: `X_[j,k]`, `K_[j,k]` and `i_[j]` are the two-
and one-level matrices of types `X`, `K` and `i`. -/
def mat : Gen n → Matrix (Fin n) (Fin n) ℂ
  | .X j k _ => twoLevel j k Xmat
  | .K j k _ => twoLevel j k Kmat
  | .i j => oneLevel j I

theorem mat_mem_unitaryGroup (x : Gen n) : mat x ∈ unitaryGroup (Fin n) ℂ := by
  cases x with
  | X j k h => exact levelMat_mem_unitaryGroup (injective_pair h.ne) Xmat_mem_unitaryGroup
  | K j k h => exact levelMat_mem_unitaryGroup (injective_pair h.ne) Kmat_mem_unitaryGroup
  | i j => exact levelMat_mem_unitaryGroup (injective_single j) I_mem_unitaryGroup

theorem I_mem_ZHalfI : I ∈ ZHalfI := Subring.subset_closure (by simp)

theorem inv_one_add_I_mem_ZHalfI : (1 + I)⁻¹ ∈ ZHalfI := by
  rw [inv_one_add_I, div_eq_mul_inv]
  exact ZHalfI.mul_mem (ZHalfI.sub_mem ZHalfI.one_mem I_mem_ZHalfI)
    (Subring.subset_closure (by simp))

theorem mat_mem_ZHalfI (x : Gen n) (a b : Fin n) : mat x a b ∈ ZHalfI := by
  cases x with
  | X j k h =>
    refine levelMat_mem (injective_pair h.ne) (fun p q => ?_) a b
    fin_cases p <;> fin_cases q <;> simp [Xmat, ZHalfI.zero_mem, ZHalfI.one_mem]
  | K j k h =>
    refine levelMat_mem (injective_pair h.ne) (fun p q => ?_) a b
    fin_cases p <;> fin_cases q <;>
      simp [Kmat, inv_one_add_I_mem_ZHalfI, ZHalfI.neg_mem inv_one_add_I_mem_ZHalfI]
  | i j =>
    refine levelMat_mem (injective_single j) (fun p q => ?_) a b
    fin_cases p; fin_cases q; simpa using I_mem_ZHalfI

/-- The semantics: each generator as an element of `Uₙ(ℤ[1/2, i])`. -/
def sem (n : ℕ) (x : Gen n) : U_ZHalfI n :=
  ⟨⟨mat x, mat_mem_unitaryGroup x⟩, mat_mem_ZHalfI x⟩

@[simp] theorem coe_sem (x : Gen n) : ((sem n x : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = mat x :=
  rfl

end

end QCert.BianSelingerUn
