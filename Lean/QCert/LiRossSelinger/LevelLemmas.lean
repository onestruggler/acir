/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# More on level matrices

`levelMat f M` (the framework's `QCert.Matrix.Level`) composes along the
index map (`levelMat_comp`), is multiplicative for injective `f`
(`levelMat_mul`), and commutes with ring homomorphisms (`levelMat_map`).
-/
import QCert.Matrix.Level

-- Keep these helpers local to this development: `LevelCalc` has a
-- `QCert.levelMat_mul` in the opposite orientation.
namespace QCert.LiRossSelinger

open Matrix

variable {R S : Type*} [CommRing R] [CommRing S] {n m k : ℕ}

theorem embedMat_comp (f : Fin m → Fin n) (g : Fin k → Fin m) :
    embedMat (R := R) (f ∘ g) = embedMat f * embedMat g := by
  ext i l
  simp only [embedMat, mul_apply, Function.comp]
  rw [Finset.sum_eq_single (g l)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem levelMat_comp (f : Fin m → Fin n) (g : Fin k → Fin m) (M : Matrix (Fin k) (Fin k) R) :
    levelMat (f ∘ g) M = levelMat f (levelMat g M) := by
  simp only [levelMat, embedMat_comp, add_sub_cancel_left, transpose_mul, Matrix.mul_assoc]

theorem levelMat_one (f : Fin m → Fin n) : levelMat f (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  simp [levelMat]

theorem levelMat_mul {f : Fin m → Fin n} (hf : Function.Injective f)
    (A B : Matrix (Fin m) (Fin m) R) : levelMat f A * levelMat f B = levelMat f (A * B) := by
  have hE := embedMat_transpose_mul (R := R) hf
  set E := embedMat (R := R) f
  have key : E * (A - 1) * Eᵀ * (E * (B - 1) * Eᵀ) = E * ((A - 1) * (B - 1)) * Eᵀ := by
    calc E * (A - 1) * Eᵀ * (E * (B - 1) * Eᵀ) = E * (A - 1) * (Eᵀ * E) * (B - 1) * Eᵀ := by
          simp only [Matrix.mul_assoc]
      _ = E * ((A - 1) * (B - 1)) * Eᵀ := by rw [hE, Matrix.mul_one, Matrix.mul_assoc E]
  have hAB : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  simp only [levelMat]
  rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, key, hAB,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem levelMat_list_prod {f : Fin m → Fin n} (hf : Function.Injective f)
    (l : List (Matrix (Fin m) (Fin m) R)) : (l.map (levelMat f)).prod = levelMat f l.prod := by
  induction l with
  | nil => simp [levelMat_one]
  | cons A l ih => rw [List.map_cons, List.prod_cons, ih, levelMat_mul hf, List.prod_cons]

theorem embedMat_map (φ : R →+* S) (f : Fin m → Fin n) :
    (embedMat (R := R) f).map φ = embedMat f := by
  ext i j; simp only [embedMat, map_apply]; split_ifs <;> simp

theorem levelMat_map (φ : R →+* S) (f : Fin m → Fin n) (M : Matrix (Fin m) (Fin m) R) :
    (levelMat f M).map φ = levelMat f (M.map φ) := by
  have h1 : ((1 : Matrix (Fin n) (Fin n) R) + embedMat f * (M - 1) * (embedMat f)ᵀ).map φ =
      φ.mapMatrix (1 + embedMat f * (M - 1) * (embedMat f)ᵀ) := rfl
  have h2 : (M - 1).map φ = M.map φ - 1 := by
    rw [show (M - 1).map φ = φ.mapMatrix (M - 1) from rfl, map_sub, map_one]; rfl
  rw [levelMat, levelMat, h1, map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_mul,
    Matrix.map_mul, embedMat_map, Matrix.transpose_map, embedMat_map, h2]

end QCert.LiRossSelinger
