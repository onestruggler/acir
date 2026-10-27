/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): semantics

The semantics `⟦·⟧_O` of `Σ₁` in `O(8, 𝔻)` (the orthogonal `8 × 8`
matrices over `𝔻 = ℤ[1/2]`, `O_ZHalf 8` of the framework) and `⟦·⟧_H` of
`Σ₂` in `TofH(3)`, the orthogonal matrices `M/√2^k` with `M` an integer
matrix (`L₈` of Li–Ross–Selinger, Definition 5.1); the gate matrices are
those of `Matrices.lean`, over `ℝ` with `s = 1/√2`.
-/
import QCert.ToffoliHadamard.Eval

namespace QCert.ToffoliHadamard

open Matrix QCert.ListMat

/-- `O(8, 𝔻)`. -/
abbrev O8D : Subgroup (unitaryGroup (Fin 8) ℝ) := O_ZHalf 8

/-- `TofH(3)`: the orthogonal `8 × 8` matrices `M/√2^k`, `M` an integer matrix. -/
abbrev TofH3 : Subgroup (unitaryGroup (Fin 8) ℝ) := LiRossSelinger.L 8

noncomputable section

/-- The real matrix of a letter of `Σ₁`. -/
def semMat (g : Sym1) : Matrix (Fin 8) (Fin 8) ℝ := gateMat (Real.sqrt 2)⁻¹ g

/-- The real matrix of `H₂`. -/
def semH2 : Matrix (Fin 8) (Fin 8) ℝ := matH2 (Real.sqrt 2)⁻¹

/-! ## Membership -/

theorem semMat_eq (g : Sym1) : semMat g = (gateMat QSqrt2.invSqrt2 g).map QSqrt2.toR := by
  rw [gateMat_map, QSqrt2.toR_invSqrt2]; rfl

theorem semH2_eq : semH2 = (matH2 QSqrt2.invSqrt2).map QSqrt2.toR := by
  rw [matH2_map, QSqrt2.toR_invSqrt2]; rfl

theorem gateMatQ_transpose (g : Sym1) :
    (gateMat QSqrt2.invSqrt2 g)ᵀ = gateMat QSqrt2.invSqrt2 g := by
  cases g <;> decide +kernel

theorem gateMatQ_sq (g : Sym1) :
    gateMat QSqrt2.invSqrt2 g * gateMat QSqrt2.invSqrt2 g = 1 := by
  have h : evalW [g, g] = evalW [] := by cases g <;> decide +kernel
  have := congrArg (ListMat.toMat 8) h
  simpa [toMat_evalW] using this

theorem gateMatQ_entries (g : Sym1) (i j : Fin 8) :
    (gateMat QSqrt2.invSqrt2 g i j).a1 = 0 ∧ ((gateMat QSqrt2.invSqrt2 g i j).a0 * 2).den = 1 := by
  revert i j; cases g <;> decide +kernel

theorem semMat_mem (g : Sym1) : semMat g ∈ unitaryGroup (Fin 8) ℝ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    semMat_eq, ← Matrix.transpose_map, gateMatQ_transpose, ← Matrix.map_mul, gateMatQ_sq,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem toR_mem_ZHalf {x : QSqrt2} (h1 : x.a1 = 0) (h2 : (x.a0 * 2).den = 1) :
    QSqrt2.toR x ∈ ZHalf := by
  have e : ((x.a0 * 2).num : ℚ) = x.a0 * 2 := Rat.coe_int_num_of_den_eq_one h2
  have : QSqrt2.toR x = ((x.a0 * 2).num : ℝ) * 2⁻¹ := by
    simp only [QSqrt2.toR, Quadratic.lift_apply, h1, Rat.cast_zero, zero_mul, add_zero]
    have e' : (((x.a0 * 2).num : ℚ) : ℝ) = ((x.a0 * 2 : ℚ) : ℝ) := by rw [e]
    rw [Rat.cast_intCast] at e'
    rw [e']; push_cast; ring
  rw [this]
  exact ZHalf.mul_mem (intCast_mem ZHalf _) LiRossSelinger.half_mem_ZHalf

theorem semMat_entries (g : Sym1) (i j : Fin 8) : semMat g i j ∈ ZHalf := by
  rw [semMat_eq, map_apply]
  exact toR_mem_ZHalf (gateMatQ_entries g i j).1 (gateMatQ_entries g i j).2

/-- `H₂ = (1/√2) N` with `N = I ⊗ I ⊗ [[1, 1], [1, −1]]`. -/
def intH2 : Matrix (Fin 8) (Fin 8) ℤ := fun i j =>
  if (i : ℕ) / 2 = (j : ℕ) / 2 then (if (i : ℕ) % 2 = 1 ∧ (j : ℕ) % 2 = 1 then -1 else 1) else 0

theorem matH2Q_eq : matH2 QSqrt2.invSqrt2 = QSqrt2.invSqrt2 • intH2.map (Int.cast) := by
  decide +kernel

theorem semH2_mem : semH2 ∈ unitaryGroup (Fin 8) ℝ := by
  have hT : (matH2 QSqrt2.invSqrt2)ᵀ = matH2 QSqrt2.invSqrt2 := by decide +kernel
  have hsq : matH2 QSqrt2.invSqrt2 * matH2 QSqrt2.invSqrt2 = 1 := by
    have h : actH2.apply 8 (actH2.apply 8 (one 8)) = one 8 := by decide +kernel
    have := congrArg (ListMat.toMat 8) h
    rwa [Act.toMat_apply, Act.toMat_apply, toMat_one, Matrix.mul_one, actH2_toMat] at this
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    semH2_eq, ← Matrix.transpose_map, hT, ← Matrix.map_mul, hsq,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem semH2_scaled : semH2 = (Real.sqrt 2 ^ 1)⁻¹ • intH2.map (Int.cast : ℤ → ℝ) := by
  rw [semH2_eq, matH2Q_eq, Matrix.map_smul', pow_one, ← QSqrt2.toR_invSqrt2]
  · congr 1; ext i j; simp
  · intro a b; exact map_mul _ _ _

/-! ## The semantics -/

/-- `⟦·⟧_O`: the semantics of `Σ₁` in `O(8, 𝔻)`. -/
def sem1 (g : Sym1) : O8D :=
  ⟨⟨semMat g, semMat_mem g⟩, (mem_unitaryOver).2 (semMat_entries g)⟩

/-- `⟦·⟧_H`: the semantics of `Σ₂` in `TofH(3)`. -/
def sem2 : Sym2 → TofH3
  | .g x => ⟨(sem1 x).1, LiRossSelinger.O_ZHalf_le_L (sem1 x).2⟩
  | .H2 => ⟨⟨semH2, semH2_mem⟩, ⟨1, intH2, semH2_scaled⟩⟩

end

end QCert.ToffoliHadamard
