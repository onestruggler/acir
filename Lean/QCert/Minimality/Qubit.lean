/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The common qubit interpretation (Section 3.1)

The interpretation `⟦·⟧⁽²⁾` of the common qubit signature `Σ⁽²⁾`
(Definition 13): `⟦ω₈⟧ = e^{iπ/4}`, `⟦-⟧ = -1`,
`⟦H⟧ |x⟩ = (1/√2) Σₖ (-1)^{xk} |k⟩`, `⟦X⟧ |x⟩ = |1 - x⟩`,
`⟦Z⟧ |x⟩ = (-1)^x |x⟩`, `⟦S⟧ |x⟩ = i^x |x⟩`, `⟦T⟧ |x⟩ = e^{iπx/4} |x⟩`,
`⟦CNOT⟧ |x, y⟩ = |x, x ⊕ y⟩` and `⟦CS⟧ |x, y⟩ = i^{xy} |x, y⟩`, with `x`
on the top wire (wire `1` here), and the swap.  A matrix `M : Op ℂ 2 k` has
entry `M s t = ⟨s| M |t⟩`.

Each gate is also given over ℤ[ω], the Hadamard scaled by `√2`
(`hadZ`, …), with the identification `*_eq` and unitarity `*_mem`.
`sem_eq_of_rows` decides an equation in a semantics built from these over
ℤ[ω].
-/
import QCert.Minimality.Scaled

namespace QCert.Minimality.Qubit

open Matrix

noncomputable section

/-- `1/√2`. -/
abbrev invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- `⟦H⟧ |x⟩ = (1/√2) Σₖ (-1)^{xk} |k⟩`. -/
def hadamardC : Op ℂ 2 1 := fun s t => invSqrt2 * (-1) ^ ((s 0 : ℕ) * (t 0 : ℕ))

/-- `⟦X⟧ |x⟩ = |1 - x⟩`. -/
def xC : Op ℂ 2 1 := fun s t => if s 0 = t 0 then 0 else 1

/-- `⟦Z⟧ |x⟩ = (-1)^x |x⟩`. -/
def zC : Op ℂ 2 1 := fun s t => if s 0 = t 0 then (-1) ^ (s 0 : ℕ) else 0

/-- `⟦S⟧ |x⟩ = i^x |x⟩`. -/
def sC : Op ℂ 2 1 := fun s t => if s 0 = t 0 then Complex.I ^ (s 0 : ℕ) else 0

/-- `⟦T⟧ |x⟩ = e^{iπx/4} |x⟩`. -/
def tC : Op ℂ 2 1 := fun s t => if s 0 = t 0 then QCert.ω ^ (s 0 : ℕ) else 0

/-- `⟦CNOT⟧ |x, y⟩ = |x, x ⊕ y⟩`, `x` on wire `1`. -/
def cnotC : Op ℂ 2 2 := fun s t =>
  if s 1 = t 1 ∧ (s 0 : ℕ) = ((t 0 : ℕ) + (t 1 : ℕ)) % 2 then 1 else 0

/-- `⟦CS⟧ |x, y⟩ = i^{xy} |x, y⟩`. -/
def csC : Op ℂ 2 2 := fun s t =>
  if s 0 = t 0 ∧ s 1 = t 1 then Complex.I ^ ((s 0 : ℕ) * (s 1 : ℕ)) else 0

/-- The swap of two wires. -/
def swapC : Op ℂ 2 2 := fun s t => if s 0 = t 1 ∧ s 1 = t 0 then 1 else 0

end

/-! ### Over ℤ[ω] -/

/-- `√2 ⟦H⟧`. -/
def hadZ : Op ZOmega 2 1 := fun s t => (-1) ^ ((s 0 : ℕ) * (t 0 : ℕ))
def xZ : Op ZOmega 2 1 := fun s t => if s 0 = t 0 then 0 else 1
def zZ : Op ZOmega 2 1 := fun s t => if s 0 = t 0 then (-1) ^ (s 0 : ℕ) else 0
def sZ : Op ZOmega 2 1 := fun s t => if s 0 = t 0 then ZOmega.I ^ (s 0 : ℕ) else 0
def tZ : Op ZOmega 2 1 := fun s t => if s 0 = t 0 then ZOmega.ω ^ (s 0 : ℕ) else 0
def cnotZ : Op ZOmega 2 2 := fun s t =>
  if s 1 = t 1 ∧ (s 0 : ℕ) = ((t 0 : ℕ) + (t 1 : ℕ)) % 2 then 1 else 0
def csZ : Op ZOmega 2 2 := fun s t =>
  if s 0 = t 0 ∧ s 1 = t 1 then ZOmega.I ^ ((s 0 : ℕ) * (s 1 : ℕ)) else 0
def swapZ : Op ZOmega 2 2 := fun s t => if s 0 = t 1 ∧ s 1 = t 0 then 1 else 0

noncomputable section

theorem hadamardC_eq : hadamardC = invSqrt2 ^ 1 • hadZ.map ZOmega.toC := by
  ext s t; simp [hadamardC, hadZ]

theorem xC_eq : xC = invSqrt2 ^ 0 • xZ.map ZOmega.toC := by
  ext s t; simp only [xC, xZ, pow_zero, one_smul, Matrix.map_apply]; split_ifs <;> simp

theorem zC_eq : zC = invSqrt2 ^ 0 • zZ.map ZOmega.toC := by
  ext s t; simp only [zC, zZ, pow_zero, one_smul, Matrix.map_apply]; split_ifs <;> simp

theorem sC_eq : sC = invSqrt2 ^ 0 • sZ.map ZOmega.toC := by
  ext s t; simp only [sC, sZ, pow_zero, one_smul, Matrix.map_apply]
  split_ifs <;> simp [ZOmega.toC_I]

theorem tC_eq : tC = invSqrt2 ^ 0 • tZ.map ZOmega.toC := by
  ext s t; simp only [tC, tZ, pow_zero, one_smul, Matrix.map_apply]
  split_ifs <;> simp [ZOmega.ω, ZOmega.toC_X]

theorem cnotC_eq : cnotC = invSqrt2 ^ 0 • cnotZ.map ZOmega.toC := by
  ext s t; simp only [cnotC, cnotZ, pow_zero, one_smul, Matrix.map_apply]; split_ifs <;> simp

theorem csC_eq : csC = invSqrt2 ^ 0 • csZ.map ZOmega.toC := by
  ext s t; simp only [csC, csZ, pow_zero, one_smul, Matrix.map_apply]
  split_ifs <;> simp [ZOmega.toC_I]

theorem swapC_eq : swapC = invSqrt2 ^ 0 • swapZ.map ZOmega.toC := by
  ext s t; simp only [swapC, swapZ, pow_zero, one_smul, Matrix.map_apply]; split_ifs <;> simp

theorem invSqrt2_star : star invSqrt2 = invSqrt2 := by
  simp [invSqrt2, Complex.conj_ofReal]

theorem invSqrt2_sq_mul_two : invSqrt2 ^ (2 * 1) * ZOmega.toC 2 = 1 := by
  have h2 := QCert.sqrt2_sq
  simp only [invSqrt2, mul_one, map_ofNat, inv_pow, h2]
  norm_num

theorem invSqrt2_pow_zero : invSqrt2 ^ (2 * 0) * ZOmega.toC 1 = 1 := by simp

/-- A scaled ℤ[ω] matrix is unitary when `A A^† = c • 1` and `(1/√2)^{2e} c = 1`. -/
theorem mem_of_int {k : ℕ} (e : ℕ) (A : Op ZOmega 2 k) (c : ZOmega)
    (h : A * (Matrix.of fun s t => ZOmega.conj (A t s)) = c • 1)
    (hc : invSqrt2 ^ (2 * e) * ZOmega.toC c = 1) :
    invSqrt2 ^ e • A.map ZOmega.toC ∈ unitaryGroup (State 2 k) ℂ :=
  mem_unitaryGroup_of_int ZOmega.toC ZOmega.conj ZOmega.toC_conj _ invSqrt2_star e A c h hc

theorem hadamardC_mem : hadamardC ∈ unitaryGroup (State 2 1) ℂ := by
  rw [hadamardC_eq]; exact mem_of_int 1 _ 2 (by decide +kernel) invSqrt2_sq_mul_two

theorem xC_mem : xC ∈ unitaryGroup (State 2 1) ℂ := by
  rw [xC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

theorem zC_mem : zC ∈ unitaryGroup (State 2 1) ℂ := by
  rw [zC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

theorem sC_mem : sC ∈ unitaryGroup (State 2 1) ℂ := by
  rw [sC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

theorem tC_mem : tC ∈ unitaryGroup (State 2 1) ℂ := by
  rw [tC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

theorem cnotC_mem : cnotC ∈ unitaryGroup (State 2 2) ℂ := by
  rw [cnotC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

theorem csC_mem : csC ∈ unitaryGroup (State 2 2) ℂ := by
  rw [csC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

theorem swapC_mem : swapC ∈ unitaryGroup (State 2 2) ℂ := by
  rw [swapC_eq]; exact mem_of_int 0 _ 1 (by decide +kernel) invSqrt2_pow_zero

theorem ω_mem : QCert.ω ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self, ZOmega.star_ω]
  have h4 := QCert.ω_pow_four
  linear_combination (-1 : ℂ) * h4

theorem minus_one_mem : (-1 : ℂ) ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self]; simp

/-- An equation between circuits holds in a qubit semantics built from
scaled ℤ[ω] matrices when the scaled integer row tries agree. -/
theorem sem_eq_of_rows {Gate : ℕ → Type} (sem : GateSem Gate ℂ 2) (S : ScaledOps Gate ZOmega 2)
    (hS : sem.toOps = S.toOps ZOmega.toC invSqrt2) {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (S.ex v - S.ex w)) (evalRows S.ops n w) =
      (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (S.ex w - S.ex v)) (evalRows S.ops n v)) :
    sem.sem n w = sem.sem n v := by
  apply Subtype.ext
  rw [GateSem.sem_val, GateSem.sem_val, hS]
  refine S.eval_toOps_eq_of_rows ZOmega.toC invSqrt2 _ ZOmega.sqrt2 ZOmega.toC_sqrt2 ?_ h
  exact mul_inv_cancel₀ QCert.sqrt2_ne_zero

end

/-- The hypothesis of `independent_of_proj` for one axiom, from a decision
on row tries: the integer matrices of the two sides, scaled to balance the
factors `1/√2`, differ by the unit `c`. -/
theorem projHyp {Gate : ℕ → Type} (S : ScaledOps Gate ZOmega 2) (c : ZOmega)
    (hc : IsUnit (ZOmega.toQ c)) {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (S.ex v - S.ex w)) (evalRows S.ops n w) =
      (rowsRep 2 n).ops.smul (c * ZOmega.sqrt2 ^ (S.ex w - S.ex v)) (evalRows S.ops n v)) :
    ∃ x y : ZOmega, IsUnit (ZOmega.toQ x) ∧ IsUnit (ZOmega.toQ y) ∧
      x • S.ops.eval n w = y • S.ops.eval n v :=
  ⟨_, _, by rw [map_pow]; exact ZOmega.isUnit_toQ_sqrt2.pow _,
    by rw [map_mul, map_pow]; exact hc.mul (ZOmega.isUnit_toQ_sqrt2.pow _),
    smul_eval_eq_of_evalRows S.ops _ _ h⟩

theorem isUnit_toQ_one : IsUnit (ZOmega.toQ 1) := by rw [map_one]; exact isUnit_one

theorem isUnit_toQ_neg_one : IsUnit (ZOmega.toQ (-1)) := by
  rw [map_neg, map_one]; exact isUnit_one.neg

end QCert.Minimality.Qubit
