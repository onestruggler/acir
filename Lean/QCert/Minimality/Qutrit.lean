/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The qutrit Clifford interpretation (Section 3.2)

Blake (FSCD 2026), Definition 17: `⟦ω₁₂⟧ = e^{iπ/6}`,
`⟦H⟧ |x⟩ = (1/√3) Σₖ e^{2πi xk/3} |k⟩`, `⟦S⟧ |x⟩ = e^{iπ x(x-1)/3} |x⟩`,
`⟦CNOT⟧ |x, y⟩ = |x, (x + y) mod 3⟩` (`x` on the top wire, wire `1`), and the
swap.  With `ζ = ζ₁₂ = e^{iπ/6}` (`ZZeta.ζ12_eq_exp`):
`e^{2πi xk/3} = ζ^{4xk}` and `e^{iπ x(x-1)/3} = ζ^{2x(x-1)}`.

Each gate is also given over ℤ[ζ], the Hadamard scaled by `√3`, with the
identification `*_eq` and unitarity `*_mem`.
-/
import QCert.Minimality.Scaled

namespace QCert.Minimality.Qutrit

open Matrix ZZeta

noncomputable section

/-- `1/√3`. -/
abbrev invSqrt3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)⁻¹

/-- `⟦H⟧ |x⟩ = (1/√3) Σₖ e^{2πi xk/3} |k⟩`, with `e^{2πi xk/3} = ζ₁₂^{4xk}`. -/
def hadamardC : Op ℂ 3 1 := fun s t => invSqrt3 * ζ12 ^ (4 * ((s 0 : ℕ) * (t 0 : ℕ)))

/-- `⟦S⟧ |x⟩ = e^{iπ x(x-1)/3} |x⟩ = ζ₁₂^{2x(x-1)} |x⟩`. -/
def sC : Op ℂ 3 1 := fun s t =>
  if s 0 = t 0 then ζ12 ^ (2 * ((s 0 : ℕ) * ((s 0 : ℕ) - 1))) else 0

/-- `⟦CNOT⟧ |x, y⟩ = |x, (x + y) mod 3⟩`, `x` on wire `1`. -/
def cnotC : Op ℂ 3 2 := fun s t =>
  if s 1 = t 1 ∧ (s 0 : ℕ) = ((t 0 : ℕ) + (t 1 : ℕ)) % 3 then 1 else 0

/-- The swap of two qutrit wires. -/
def swapC : Op ℂ 3 2 := fun s t => if s 0 = t 1 ∧ s 1 = t 0 then 1 else 0

end

/-! ### Over ℤ[ζ] -/

/-- `√3 ⟦H⟧`. -/
def hadZ : Op ZZeta 3 1 := fun s t => ζ ^ (4 * ((s 0 : ℕ) * (t 0 : ℕ)))
def sZ : Op ZZeta 3 1 := fun s t =>
  if s 0 = t 0 then ζ ^ (2 * ((s 0 : ℕ) * ((s 0 : ℕ) - 1))) else 0
def cnotZ : Op ZZeta 3 2 := fun s t =>
  if s 1 = t 1 ∧ (s 0 : ℕ) = ((t 0 : ℕ) + (t 1 : ℕ)) % 3 then 1 else 0
def swapZ : Op ZZeta 3 2 := fun s t => if s 0 = t 1 ∧ s 1 = t 0 then 1 else 0

noncomputable section

theorem hadamardC_eq : hadamardC = invSqrt3 ^ 1 • hadZ.map ZZeta.toC := by
  ext s t; simp [hadamardC, hadZ, ZZeta.ζ, ZZeta.toC_X]

theorem sC_eq : sC = invSqrt3 ^ 0 • sZ.map ZZeta.toC := by
  ext s t; simp only [sC, sZ, pow_zero, one_smul, Matrix.map_apply]
  split_ifs <;> simp [ZZeta.ζ, ZZeta.toC_X]

theorem cnotC_eq : cnotC = invSqrt3 ^ 0 • cnotZ.map ZZeta.toC := by
  ext s t; simp only [cnotC, cnotZ, pow_zero, one_smul, Matrix.map_apply]; split_ifs <;> simp

theorem swapC_eq : swapC = invSqrt3 ^ 0 • swapZ.map ZZeta.toC := by
  ext s t; simp only [swapC, swapZ, pow_zero, one_smul, Matrix.map_apply]; split_ifs <;> simp

theorem invSqrt3_star : star invSqrt3 = invSqrt3 := by
  simp [invSqrt3, Complex.conj_ofReal]

theorem invSqrt3_sq_mul_three : invSqrt3 ^ (2 * 1) * ZZeta.toC 3 = 1 := by
  have h3 := ZZeta.sqrt3_sq
  simp only [invSqrt3, mul_one, map_ofNat, inv_pow, h3]
  norm_num

theorem invSqrt3_pow_zero : invSqrt3 ^ (2 * 0) * ZZeta.toC 1 = 1 := by simp

/-- A scaled ℤ[ζ] matrix is unitary when `A A^† = c • 1` and `(1/√3)^{2e} c = 1`. -/
theorem mem_of_int {k : ℕ} (e : ℕ) (A : Op ZZeta 3 k) (c : ZZeta)
    (h : A * (Matrix.of fun s t => ZZeta.conj (A t s)) = c • 1)
    (hc : invSqrt3 ^ (2 * e) * ZZeta.toC c = 1) :
    invSqrt3 ^ e • A.map ZZeta.toC ∈ unitaryGroup (State 3 k) ℂ :=
  mem_unitaryGroup_of_int ZZeta.toC ZZeta.conj ZZeta.toC_conj _ invSqrt3_star e A c h hc

theorem hadamardC_mem : hadamardC ∈ unitaryGroup (State 3 1) ℂ := by
  rw [hadamardC_eq]; exact mem_of_int 1 _ 3 (by decide +kernel) invSqrt3_sq_mul_three

theorem sC_mem : sC ∈ unitaryGroup (State 3 1) ℂ := by
  rw [sC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt3_pow_zero

theorem cnotC_mem : cnotC ∈ unitaryGroup (State 3 2) ℂ := by
  rw [cnotC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt3_pow_zero

theorem swapC_mem : swapC ∈ unitaryGroup (State 3 2) ℂ := by
  rw [swapC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt3_pow_zero

theorem ζ12_mem : ζ12 ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self, star_ζ12]
  have h4 := ζ12_pow_four
  have h3 := ζ12_pow_three
  simp only [Int.cast_one, Int.cast_neg, one_mul] at h4
  linear_combination (-1 : ℂ) * h4

/-- An equation between circuits holds in a qutrit semantics built from
scaled ℤ[ζ] matrices when the scaled integer row tries agree. -/
theorem sem_eq_of_rows {Gate : ℕ → Type} (sem : GateSem Gate ℂ 3) (S : ScaledOps Gate ZZeta 3)
    (hS : sem.toOps = S.toOps ZZeta.toC invSqrt3) {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 3 n).ops.smul (ZZeta.sqrt3 ^ (S.ex v - S.ex w)) (evalRows S.ops n w) =
      (rowsRep 3 n).ops.smul (ZZeta.sqrt3 ^ (S.ex w - S.ex v)) (evalRows S.ops n v)) :
    sem.sem n w = sem.sem n v := by
  apply Subtype.ext
  rw [GateSem.sem_val, GateSem.sem_val, hS]
  refine S.eval_toOps_eq_of_rows ZZeta.toC invSqrt3 _ ZZeta.sqrt3 ZZeta.toC_sqrt3 ?_ h
  exact mul_inv_cancel₀ ZZeta.sqrt3_ne_zero

end

/-- The hypothesis of `independent_of_proj` for one axiom, from a decision
on row tries: the integer matrices of the two sides, scaled to balance the
factors `1/√3`, differ by the unit `c`. -/
theorem projHyp {Gate : ℕ → Type} (S : ScaledOps Gate ZZeta 3) (c : ZZeta)
    (hc : IsUnit (ZZeta.toQ c)) {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 3 n).ops.smul (ZZeta.sqrt3 ^ (S.ex v - S.ex w)) (evalRows S.ops n w) =
      (rowsRep 3 n).ops.smul (c * ZZeta.sqrt3 ^ (S.ex w - S.ex v)) (evalRows S.ops n v)) :
    ∃ x y : ZZeta, IsUnit (ZZeta.toQ x) ∧ IsUnit (ZZeta.toQ y) ∧
      x • S.ops.eval n w = y • S.ops.eval n v :=
  ⟨_, _, by rw [map_pow]; exact ZZeta.isUnit_toQ_sqrt3.pow _,
    by rw [map_mul, map_pow]; exact hc.mul (ZZeta.isUnit_toQ_sqrt3.pow _),
    smul_eval_eq_of_evalRows S.ops _ _ h⟩

end QCert.Minimality.Qutrit
