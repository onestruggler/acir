/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Matrices acting on a few basis vectors

For an injective `f : Fin m → Fin n` and an `m × m` matrix `M`, the
*m-level matrix* `levelMat f M` acts as `M` on the basis vectors
`f 0, …, f (m - 1)` and as the identity on the others:
`levelMat f M = 1 + E (M - 1) Eᵀ`, `E` the `n × m` matrix with `E (f k) k = 1`.
Two-level matrices (`m = 2`) and one-level matrices (`m = 1`) generate the
groups of the exact synthesis papers.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Matrix.Basis

namespace QCert

open Matrix

variable {R : Type*} [CommRing R] {n m : ℕ}

/-- The `n × m` matrix sending the `k`-th basis vector to the `f k`-th. -/
def embedMat (f : Fin m → Fin n) : Matrix (Fin n) (Fin m) R :=
  fun i k => if f k = i then 1 else 0

/-- The matrix acting as `M` on the basis vectors `f 0, …, f (m - 1)` and
as the identity elsewhere. -/
def levelMat (f : Fin m → Fin n) (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin n) (Fin n) R :=
  1 + embedMat f * (M - 1) * (embedMat f)ᵀ

theorem embedMat_transpose_mul {f : Fin m → Fin n} (hf : Function.Injective f) :
    (embedMat f)ᵀ * embedMat f = (1 : Matrix (Fin m) (Fin m) R) := by
  ext k l
  simp only [mul_apply, transpose_apply, embedMat, one_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [Finset.sum_eq_single (f k)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hkl]
    · intro i _
      by_cases h1 : f k = i
      · subst h1
        have : f l ≠ f k := hf.ne (Ne.symm hkl)
        simp [this]
      · simp [h1]

private theorem levelMat_apply_aux (f : Fin m → Fin n) (M : Matrix (Fin m) (Fin m) R)
    (i j : Fin n) :
    levelMat f M i j = (1 : Matrix (Fin n) (Fin n) R) i j +
      ∑ k, ∑ l, (if f k = i then 1 else 0) * (M - 1) k l * (if f l = j then 1 else 0) := by
  simp only [levelMat, add_apply, mul_apply, embedMat, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- On the basis vectors it moves, a level matrix is `M`. -/
theorem levelMat_apply_apply {f : Fin m → Fin n} (hf : Function.Injective f)
    (M : Matrix (Fin m) (Fin m) R) (k l : Fin m) : levelMat f M (f k) (f l) = M k l := by
  rw [levelMat_apply_aux, Finset.sum_eq_single k (fun k' _ hk' => by simp [hf.ne hk']) (by simp),
    Finset.sum_eq_single l (fun l' _ hl' => by simp [hf.ne hl']) (by simp)]
  simp only [if_true, one_mul, mul_one, sub_apply, one_apply, hf.eq_iff]
  split_ifs <;> ring

/-- Off the basis vectors it moves, a level matrix is the identity. -/
theorem levelMat_apply_of_left {f : Fin m → Fin n} (M : Matrix (Fin m) (Fin m) R)
    {i : Fin n} (hi : ∀ k, f k ≠ i) (j : Fin n) :
    levelMat f M i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [levelMat_apply_aux, Finset.sum_eq_zero (fun k _ => by simp [hi k]), add_zero]

theorem levelMat_apply_of_right {f : Fin m → Fin n} (M : Matrix (Fin m) (Fin m) R)
    (i : Fin n) {j : Fin n} (hj : ∀ l, f l ≠ j) :
    levelMat f M i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [levelMat_apply_aux, Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero
    (fun l _ => by simp [hj l])), add_zero]

section Star

variable [StarRing R]

theorem conjTranspose_embedMat (f : Fin m → Fin n) :
    (embedMat (R := R) f)ᴴ = (embedMat f)ᵀ := by
  ext i j; by_cases h : f i = j <;> simp [embedMat, conjTranspose_apply, h]

theorem conjTranspose_embedMat_transpose (f : Fin m → Fin n) :
    ((embedMat (R := R) f)ᵀ)ᴴ = embedMat f := by
  ext i j; by_cases h : f j = i <;> simp [embedMat, conjTranspose_apply, h]

theorem star_levelMat (f : Fin m → Fin n) (M : Matrix (Fin m) (Fin m) R) :
    star (levelMat f M) = levelMat f (star M) := by
  simp only [levelMat, star_eq_conjTranspose, conjTranspose_add, conjTranspose_one,
    conjTranspose_mul, conjTranspose_sub, conjTranspose_embedMat,
    conjTranspose_embedMat_transpose, Matrix.mul_assoc]

/-- A level matrix of a unitary matrix is unitary. -/
theorem levelMat_mem_unitaryGroup {f : Fin m → Fin n} (hf : Function.Injective f)
    {M : Matrix (Fin m) (Fin m) R} (hM : M ∈ unitaryGroup (Fin m) R) :
    levelMat f M ∈ unitaryGroup (Fin n) R := by
  rw [mem_unitaryGroup_iff, star_levelMat]
  have hM' : M * star M = 1 := mem_unitaryGroup_iff.1 hM
  have hE := embedMat_transpose_mul (R := R) hf
  have hAB : (M - 1) * (star M - 1) = -((M - 1) + (star M - 1)) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hM']; abel
  -- (1 + E A Eᵀ)(1 + E B Eᵀ) = 1 + E A Eᵀ + E B Eᵀ + E (A B) Eᵀ, and A B = -(A + B)
  generalize hA : M - 1 = A at hAB
  generalize hB : star M - 1 = B at hAB
  simp only [levelMat, hA, hB]
  set E := embedMat (R := R) f
  have : E * A * Eᵀ * (E * B * Eᵀ) = E * (A * B) * Eᵀ := by
    calc E * A * Eᵀ * (E * B * Eᵀ) = E * A * (Eᵀ * E) * B * Eᵀ := by
          simp only [Matrix.mul_assoc]
      _ = E * (A * B) * Eᵀ := by rw [hE, Matrix.mul_one, Matrix.mul_assoc E A B]
  rw [add_mul, mul_add, mul_add]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [this, hAB, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul]
  abel

/-- The level matrix of a unitary, as a unitary. -/
def levelU (f : Fin m ↪ Fin n) (U : unitaryGroup (Fin m) R) : unitaryGroup (Fin n) R :=
  ⟨levelMat f U, levelMat_mem_unitaryGroup f.injective U.2⟩

end Star

end QCert
