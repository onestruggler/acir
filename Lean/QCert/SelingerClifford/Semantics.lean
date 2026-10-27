/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): the matrix semantics

The matrices of equation (1.1) of Selinger's paper, read on their wires
with wire `0` the least significant bit (`ofMat`).  `Z_c` is symmetric, so
the order of its two wires does not matter.
-/
import QCert.SelingerClifford.Syntax
import QCert.Circuit.Semantics
import QCert.Exact.Roots

namespace QCert.SelingerClifford

open Matrix

noncomputable section

/-- `1/√2`. -/
abbrev invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The Hadamard gate `H = (1/√2) [[1, 1], [1, -1]]` (1.1). -/
def matH : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := invSqrt2 • !![1, 1; 1, -1]

/-- `S = [[1, 0], [0, i]]` (1.1). -/
def matS : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := !![1, 0; 0, Complex.I]

/-- The controlled-`Z` gate `Z_c = diag(1, 1, 1, -1)` (1.1). -/
def matCZ : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

theorem star_ω_mul_ω : star ω * ω = 1 := by
  have h : star ω = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (1 - Complex.I) := by
    simp only [ω, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, map_add, map_one,
      Complex.conj_I, sub_eq_add_neg]
  rw [h, ω]
  have h2 := sqrt2_sq
  have h0 := sqrt2_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq, h2]
  ring

theorem ω_mem_unitary : ω ∈ unitary ℂ :=
  ⟨star_ω_mul_ω, by rw [mul_comm]; exact star_ω_mul_ω⟩

theorem invSqrt2_sq : invSqrt2 * invSqrt2 = 1 / 2 := by
  rw [← mul_inv, ← sq, sqrt2_sq, one_div]

theorem conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, Complex.conj_ofReal]

theorem matH_unitary : matH ∈ unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [mem_unitaryGroup_iff]
  have h := invSqrt2_sq
  have hc := conj_invSqrt2
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matH, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc] <;>
    linear_combination 2 * h

theorem matS_unitary : matS ∈ unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem matCZ_unitary : matCZ ∈ unitaryGroup (Fin (2 ^ 2)) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matCZ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply]

/-- The semantics of the Clifford gates (1.1). -/
def S : GateSem Gate ℂ 2 where
  scalar
    | .ω => ⟨ω, ω_mem_unitary⟩
  gate1
    | .H => ⟨ofMat matH, ofMat_mem_unitaryGroup matH_unitary⟩
    | .S => ⟨ofMat matS, ofMat_mem_unitaryGroup matS_unitary⟩
  gate2
    | .CZ => ⟨ofMat matCZ, ofMat_mem_unitaryGroup matCZ_unitary⟩
  gate3 g := nomatch g

end

end QCert.SelingerClifford
