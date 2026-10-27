/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the matrices of the generators

The generators of Definition 6 read as one- and two-level matrices
(Definitions 3, 4) of the types `X = [[0,1],[1,0]]`,
`H = (1/√2) [[1,1],[1,-1]]` and `ω = e^{iπ/4}`, as elements of the target
group `Uₙ(ℤ[1/√2, i])` (`U_ZInvSqrt2I`).
-/
import QCert.Greylyn.Syntax
import QCert.BianSelingerUn.LevelCalc
import QCert.Exact.Roots

namespace QCert.Greylyn

open Matrix Complex

noncomputable section

/-- The matrix `X`. -/
def Xmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Hadamard matrix `H = (1/√2) [[1, 1], [1, -1]]`. -/
def Hmat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.sqrt 2 : ℝ) : ℂ)⁻¹, ((Real.sqrt 2 : ℝ) : ℂ)⁻¹;
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹, -((Real.sqrt 2 : ℝ) : ℂ)⁻¹]

theorem invSqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← sq, sqrt2_sq, one_div]

theorem Xmat_mem_unitaryGroup : Xmat ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Xmat, mul_apply, Fin.sum_univ_two]

theorem Hmat_mem_unitaryGroup : Hmat ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Hmat, mul_apply, Fin.sum_univ_two, Complex.conj_ofReal]
  all_goals rw [invSqrt2_sq]; norm_num

theorem ω_mem_unitaryGroup : !![QCert.ω] ∈ unitaryGroup (Fin 1) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext a b
  fin_cases a; fin_cases b
  simp only [mul_apply, Finset.univ_unique, Finset.sum_singleton, star_apply]
  simp only [Fin.default_eq_zero, Fin.isValue, of_apply, cons_val', cons_val_fin_one,
    one_apply_eq, QCert.ω, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal,
    map_add, map_one, conj_I]
  have h : (1 + I) * (1 + -I) = 2 := by ring_nf; rw [I_sq]; ring
  calc ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (1 + I) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (1 + -I))
      = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * ((1 + I) * (1 + -I)) := by ring
    _ = 1 := by rw [invSqrt2_sq, h]; norm_num

variable {n : ℕ}

/-- The matrix of a generator: `X_[j,k]`, `H_[j,k]` and `ω_[j]` are the two-
and one-level matrices of types `X`, `H` and `ω`. -/
def mat : Gen n → Matrix (Fin n) (Fin n) ℂ
  | .X j k _ => twoLevel j k Xmat
  | .H j k _ => twoLevel j k Hmat
  | .ω j => oneLevel j QCert.ω

theorem mat_mem_unitaryGroup (x : Gen n) : mat x ∈ unitaryGroup (Fin n) ℂ := by
  cases x with
  | X j k h => exact levelMat_mem_unitaryGroup (injective_pair h.ne) Xmat_mem_unitaryGroup
  | H j k h => exact levelMat_mem_unitaryGroup (injective_pair h.ne) Hmat_mem_unitaryGroup
  | ω j => exact levelMat_mem_unitaryGroup (injective_single j) ω_mem_unitaryGroup

theorem invSqrt2_mem : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ∈ ZInvSqrt2I := Subring.subset_closure (by simp)

theorem ω_mem : QCert.ω ∈ ZInvSqrt2I :=
  ZInvSqrt2I.mul_mem invSqrt2_mem
    (ZInvSqrt2I.add_mem ZInvSqrt2I.one_mem (Subring.subset_closure (by simp)))

theorem mat_mem_ZInvSqrt2I (x : Gen n) (a b : Fin n) : mat x a b ∈ ZInvSqrt2I := by
  cases x with
  | X j k h =>
    refine levelMat_mem (injective_pair h.ne) (fun p q => ?_) a b
    fin_cases p <;> fin_cases q <;> simp [Xmat, ZInvSqrt2I.zero_mem, ZInvSqrt2I.one_mem]
  | H j k h =>
    refine levelMat_mem (injective_pair h.ne) (fun p q => ?_) a b
    fin_cases p <;> fin_cases q <;> simp [Hmat, invSqrt2_mem, ZInvSqrt2I.neg_mem invSqrt2_mem]
  | ω j =>
    refine levelMat_mem (injective_single j) (fun p q => ?_) a b
    fin_cases p; fin_cases q; simpa using ω_mem

/-- The semantics: each generator as an element of `Uₙ(ℤ[1/√2, i])`. -/
def sem (n : ℕ) (x : Gen n) : U_ZInvSqrt2I n :=
  ⟨⟨mat x, mat_mem_unitaryGroup x⟩, mat_mem_ZInvSqrt2I x⟩

@[simp] theorem coe_sem (x : Gen n) :
    ((sem n x : unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = mat x := rfl

end

end QCert.Greylyn
