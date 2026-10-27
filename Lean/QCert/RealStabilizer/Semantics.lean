/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: the matrix semantics

The matrices of §2 of Makary, Ross and Selinger, read on their wires with
wire `0` the least significant bit (`ofMat`), as real orthogonal matrices:
the target group is `unitaryGroup (State 2 n) ℝ`, the orthogonal group
`O(2ⁿ)` (the involution of `ℝ` is trivial).  `CZ` is symmetric, so the
order of its two wires does not matter.
-/
import QCert.RealStabilizer.Syntax
import QCert.Circuit.Semantics
import QCert.Exact.Roots

namespace QCert.RealStabilizer

open Matrix

noncomputable section

/-- `1/√2`. -/
abbrev invSqrt2 : ℝ := (Real.sqrt 2)⁻¹

/-- The Hadamard matrix `H = (1/√2) [[1, 1], [1, -1]]` (§2). -/
def matH : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℝ := invSqrt2 • !![1, 1; 1, -1]

/-- `Z = [[1, 0], [0, -1]]` (§2). -/
def matZ : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℝ := !![1, 0; 0, -1]

/-- `CZ = diag(1, 1, 1, -1)` (§2). -/
def matCZ : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℝ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]

theorem neg_one_mem_unitary : (-1 : ℝ) ∈ unitary ℝ := by
  rw [Unitary.mem_iff]; simp

theorem invSqrt2_sq : invSqrt2 * invSqrt2 = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

theorem matH_unitary : matH ∈ unitaryGroup (Fin (2 ^ 1)) ℝ := by
  rw [mem_unitaryGroup_iff]
  have h := invSqrt2_sq
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matH, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
    linear_combination 2 * h

theorem matZ_unitary : matZ ∈ unitaryGroup (Fin (2 ^ 1)) ℝ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem matCZ_unitary : matCZ ∈ unitaryGroup (Fin (2 ^ 2)) ℝ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matCZ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply]

/-- The semantics of the real stabilizer gates (§2), as orthogonal
matrices. -/
def S : GateSem Gate ℝ 2 where
  scalar
    | .neg => ⟨-1, neg_one_mem_unitary⟩
  gate1
    | .H => ⟨ofMat matH, ofMat_mem_unitaryGroup matH_unitary⟩
    | .Z => ⟨ofMat matZ, ofMat_mem_unitaryGroup matZ_unitary⟩
  gate2
    | .CZ => ⟨ofMat matCZ, ofMat_mem_unitaryGroup matCZ_unitary⟩
  gate3 g := nomatch g

end

end QCert.RealStabilizer
