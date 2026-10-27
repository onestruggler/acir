/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The semantics of Cliff₂ (Section 3.1)

The interpretation `⟦·⟧⁽²⁾` of Section 3.1 restricted to the gates of
Cliff₂: `⟦ω₈⟧ = e^{iπ/4}`, `⟦H⟧ |x⟩ = (1/√2) Σₖ (-1)^{xk} |k⟩`,
`⟦S⟧ |x⟩ = i^x |x⟩`, `⟦CNOT⟧ |x, y⟩ = |x, x ⊕ y⟩` (`x` on the top wire, wire
`1`), and the swap exchanges the two wires.  A matrix `M : Op ℂ 2 k` has
entry `M s t = ⟨s| M |t⟩`.

`ops` gives the same gates as integer matrices over ℤ[ω] with the Hadamard
scaled by `√2` (`scaled`); `sem_toOps` identifies the two, so that
equations between circuits are decided over ℤ[ω].
-/
import QCert.Minimality.Clifford.Syntax
import QCert.Minimality.Scaled
import QCert.Minimality.Exact

namespace QCert.Minimality.Clifford

open Matrix

noncomputable section

/-- `1/√2`. -/
abbrev invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- `⟦H⟧ |x⟩ = (1/√2) Σₖ (-1)^{xk} |k⟩`. -/
def hadamardC : Op ℂ 2 1 := fun s t => invSqrt2 * (-1) ^ ((s 0 : ℕ) * (t 0 : ℕ))

/-- `⟦S⟧ |x⟩ = i^x |x⟩`. -/
def phaseC : Op ℂ 2 1 := fun s t => if s 0 = t 0 then Complex.I ^ (s 0 : ℕ) else 0

/-- `⟦CNOT⟧ |x, y⟩ = |x, x ⊕ y⟩`, `x` on wire `1`. -/
def cnotC : Op ℂ 2 2 := fun s t =>
  if s 1 = t 1 ∧ (s 0 : ℕ) = ((t 0 : ℕ) + (t 1 : ℕ)) % 2 then 1 else 0

/-- The swap of two wires. -/
def swapC : Op ℂ 2 2 := fun s t => if s 0 = t 1 ∧ s 1 = t 0 then 1 else 0

/-! ### Integer matrices -/

/-- The gates of Cliff₂ over ℤ[ω], the Hadamard scaled by `√2`. -/
def ops : GateOps Gate ZOmega 2 where
  scalar _ := ZOmega.ω
  gate1
    | .H => fun s t => (-1) ^ ((s 0 : ℕ) * (t 0 : ℕ))
    | .S => fun s t => if s 0 = t 0 then ZOmega.I ^ (s 0 : ℕ) else 0
  gate2
    | .CX => fun s t => if s 1 = t 1 ∧ (s 0 : ℕ) = ((t 0 : ℕ) + (t 1 : ℕ)) % 2 then 1 else 0
    | .swap => fun s t => if s 0 = t 1 ∧ s 1 = t 0 then 1 else 0
  gate3 g := nomatch g

/-- The scaling: only `H` carries a factor `1/√2`. -/
def scaled : ScaledOps Gate ZOmega 2 where
  ops := ops
  e1
    | .H => 1
    | .S => 0
  e2 _ := 0
  e3 g := nomatch g

/-! ### The unitary semantics -/

theorem invSqrt2_star : star invSqrt2 = invSqrt2 := by
  simp [invSqrt2, Complex.conj_ofReal]

theorem invSqrt2_sq_mul_two : invSqrt2 ^ (2 * 1) * ZOmega.toC 2 = 1 := by
  have h0 := QCert.sqrt2_ne_zero
  have h2 := QCert.sqrt2_sq
  simp only [invSqrt2, mul_one, map_ofNat, inv_pow, h2]
  norm_num

theorem hadamardC_eq : hadamardC = invSqrt2 ^ 1 • (ops.gate1 .H).map ZOmega.toC := by
  ext s t
  simp [hadamardC, ops]

theorem phaseC_eq : phaseC = invSqrt2 ^ 0 • (ops.gate1 .S).map ZOmega.toC := by
  ext s t
  simp only [phaseC, ops, pow_zero, one_smul, Matrix.map_apply]
  split_ifs <;> simp [ZOmega.toC_I]

theorem cnotC_eq : cnotC = invSqrt2 ^ 0 • (ops.gate2 .CX).map ZOmega.toC := by
  ext s t
  simp only [cnotC, ops, pow_zero, one_smul, Matrix.map_apply]
  split_ifs <;> simp

theorem swapC_eq : swapC = invSqrt2 ^ 0 • (ops.gate2 .swap).map ZOmega.toC := by
  ext s t
  simp only [swapC, ops, pow_zero, one_smul, Matrix.map_apply]
  split_ifs <;> simp

theorem one_pow_mul_one : invSqrt2 ^ (2 * 0) * ZOmega.toC 1 = 1 := by simp

theorem ω_mem_unitary : QCert.ω ∈ unitary ℂ := by
  rw [Unitary.mem_iff_star_mul_self, ZOmega.star_ω]
  have h4 := QCert.ω_pow_four
  linear_combination (-1 : ℂ) * h4

/-- The interpretation of the gates of Cliff₂ (Section 3.1). -/
def sem : GateSem Gate ℂ 2 where
  scalar
    | .ω => ⟨QCert.ω, ω_mem_unitary⟩
  gate1
    | .H => ⟨hadamardC, by
        rw [hadamardC_eq]
        exact mem_unitaryGroup_of_int ZOmega.toC ZOmega.conj ZOmega.toC_conj _ invSqrt2_star 1 _ 2
          (by decide +kernel) invSqrt2_sq_mul_two⟩
    | .S => ⟨phaseC, by
        rw [phaseC_eq]
        exact mem_unitaryGroup_of_int ZOmega.toC ZOmega.conj ZOmega.toC_conj _ invSqrt2_star 0 _ 1
          (by decide +kernel) one_pow_mul_one⟩
  gate2
    | .CX => ⟨cnotC, by
        rw [cnotC_eq]
        exact mem_unitaryGroup_of_int ZOmega.toC ZOmega.conj ZOmega.toC_conj _ invSqrt2_star 0 _ 1
          (by decide +kernel) one_pow_mul_one⟩
    | .swap => ⟨swapC, by
        rw [swapC_eq]
        exact mem_unitaryGroup_of_int ZOmega.toC ZOmega.conj ZOmega.toC_conj _ invSqrt2_star 0 _ 1
          (by decide +kernel) one_pow_mul_one⟩
  gate3 g := nomatch g

theorem sem_toOps : sem.toOps = scaled.toOps ZOmega.toC invSqrt2 := by
  have hs : ∀ g : Gate 1, (sem.gate1 g : Op ℂ 2 1) = invSqrt2 ^ scaled.e1 g • (ops.gate1 g).map ZOmega.toC
    | .H => hadamardC_eq
    | .S => phaseC_eq
  have hs2 : ∀ g : Gate 2, (sem.gate2 g : Op ℂ 2 2) = invSqrt2 ^ scaled.e2 g • (ops.gate2 g).map ZOmega.toC
    | .CX => cnotC_eq
    | .swap => swapC_eq
  simp only [GateSem.toOps, ScaledOps.toOps]
  congr 1
  · funext c; cases c; exact ZOmega.toC_X.symm
  · funext g; exact hs g
  · funext g; exact hs2 g
  · funext g; exact nomatch g

/-- An equation between circuits holds in the semantics when the scaled
integer row tries agree. -/
theorem sem_eq_of_rows {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (scaled.ex v - scaled.ex w)) (evalRows ops n w) =
      (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (scaled.ex w - scaled.ex v)) (evalRows ops n v)) :
    sem.sem n w = sem.sem n v := by
  apply Subtype.ext
  rw [GateSem.sem_val, GateSem.sem_val, sem_toOps]
  refine scaled.eval_toOps_eq_of_rows ZOmega.toC invSqrt2 _ ZOmega.sqrt2 ZOmega.toC_sqrt2 ?_ h
  exact mul_inv_cancel₀ QCert.sqrt2_ne_zero

end

end QCert.Minimality.Clifford
