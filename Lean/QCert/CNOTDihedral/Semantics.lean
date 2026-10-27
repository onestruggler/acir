/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CNOT-dihedral circuits: the matrix semantics

The matrices of Definition 3.1 of Amy, Chen and Ross, read on their wires
with wire `0` the least significant bit (`ofMat`): the paper writes a
two-qubit state `|x₁ x₂⟩` with the upper wire first, so the upper wire
(our wire `1`) is the most significant bit, and the printed `CNOT` matrix
has its control on wire `1`.  `SWAP` is the symmetry of §2.
-/
import QCert.CNOTDihedral.Syntax
import QCert.Circuit.Semantics
import QCert.Exact.Roots

namespace QCert.CNOTDihedral

open Matrix

noncomputable section

/-- `X` (Definition 3.1). -/
def matX : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := !![0, 1; 1, 0]

/-- `T` (Definition 3.1), `ω = e^{iπ/4}`. -/
def matT : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ := !![1, 0; 0, ω]

/-- `CNOT` (Definition 3.1), control on the upper wire. -/
def matCX : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

/-- `SWAP`, the symmetry (§2). -/
def matSW : Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

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

theorem matX_unitary : matX ∈ unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

theorem matT_unitary : matT ∈ unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [mem_unitaryGroup_iff]
  have h : ω * (starRingEnd ℂ) ω = 1 := by rw [mul_comm]; exact star_ω_mul_ω
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, h]

theorem matCX_unitary : matCX ∈ unitaryGroup (Fin (2 ^ 2)) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matCX, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply]

theorem matSW_unitary : matSW ∈ unitaryGroup (Fin (2 ^ 2)) ℂ := by
  rw [mem_unitaryGroup_iff]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [matSW, Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_apply]

/-- The semantics of the CNOT-dihedral gates (Definition 3.1). -/
def S : GateSem Gate ℂ 2 where
  scalar
    | .ω => ⟨ω, ω_mem_unitary⟩
  gate1
    | .X => ⟨ofMat matX, ofMat_mem_unitaryGroup matX_unitary⟩
    | .T => ⟨ofMat matT, ofMat_mem_unitaryGroup matT_unitary⟩
  gate2
    | .CX => ⟨ofMat matCX, ofMat_mem_unitaryGroup matCX_unitary⟩
    | .SW => ⟨ofMat matSW, ofMat_mem_unitaryGroup matSW_unitary⟩
  gate3 g := nomatch g

end

end QCert.CNOTDihedral
