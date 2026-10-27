/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Matrices over ℚ(ω) read as complex matrices

General tools for the Bian–Selinger developments (`CliffordT2`,
`CliffordCS3`), not specific to either paper:

* `tensor A B`: the Kronecker product `A ⊗ B` of square matrices indexed by
  `Fin m` and `Fin n`, indexed by `Fin (m * n)` with the pair `(a, b)` at
  index `n * a + b`, the usual convention (the first factor is the most
  significant digit of the index).
* `QOmega.conj`: complex conjugation on ℚ(ω), `ω ↦ ω⁷ = -ω³`, with
  `QOmega.toC (conj x) = star (QOmega.toC x)`.
* `cmat M`: a matrix over ℚ(ω) read in `ℂ`, with `star (cmat M) = cmat Mᴴ`
  (`Mᴴ` computed over ℚ(ω), `dagQ`), and `unitaryQ`: a matrix over ℚ(ω)
  whose product with its conjugate transpose is decided to be `1` as a
  complex unitary.
-/
import QCert.Exact.Roots
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup

namespace QCert

open Matrix
open scoped Kronecker

/-- The Kronecker product `A ⊗ B`, the pair `(a, b)` at index `n * a + b`. -/
def tensor {R : Type*} [Mul R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) : Matrix (Fin (m * n)) (Fin (m * n)) R :=
  (A ⊗ₖ B).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

namespace QOmega

/-- Complex conjugation on ℚ(ω): `a₀ + a₁ω + a₂ω² + a₃ω³ ↦ a₀ - a₃ω - a₂ω² - a₁ω³`,
since `ω̄ = ω⁷ = -ω³`, `ω̄² = -ω²`, `ω̄³ = -ω`. -/
def conj : QOmega →+* QOmega where
  toFun x := ⟨x.a0, -x.a3, -x.a2, -x.a1⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp <;> ring

theorem conj_apply (x : QOmega) : conj x = ⟨x.a0, -x.a3, -x.a2, -x.a1⟩ := rfl

private theorem star_ω : star ω = -ω ^ 3 := by
  have h3 : ω ^ 3 = ω * Complex.I := by rw [pow_succ, ω_sq, mul_comm]
  rw [h3]
  show star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (1 + Complex.I)) =
    -((((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (1 + Complex.I)) * Complex.I)
  rw [star_mul', star_inv₀, star_add, star_one, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I]
  linear_combination ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I_sq

private theorem star_ratCast (q : ℚ) : star ((q : ℂ)) = (q : ℂ) := by
  have := map_ratCast (starRingEnd ℂ) q
  rwa [starRingEnd_apply] at this

theorem toC_conj (x : QOmega) : toC (conj x) = star (toC x) := by
  have h4 : ω ^ 4 = -1 := ω_pow_four
  rw [toC, Quartic.lift_apply, Quartic.lift_apply, conj_apply]
  simp only [star_add, star_mul', star_pow, star_ω, star_ratCast]
  push_cast
  linear_combination (-(x.a2 : ℂ) * ω ^ 2 + (x.a3 : ℂ) * ω * (ω ^ 4 - 1)) * h4

end QOmega

/-- The conjugate transpose of a matrix over ℚ(ω), computed over ℚ(ω). -/
def dagQ {n : Type*} (M : Matrix n n QOmega) : Matrix n n QOmega :=
  Mᵀ.map QOmega.conj

/-- A matrix over ℚ(ω) read in `ℂ`. -/
noncomputable def cmat {n : Type*} (M : Matrix n n QOmega) : Matrix n n ℂ :=
  M.map QOmega.toC

theorem star_cmat {n : Type*} (M : Matrix n n QOmega) : star (cmat M) = cmat (dagQ M) := by
  ext i j
  simp [cmat, dagQ, QOmega.toC_conj]

theorem cmat_mul {n : Type*} [Fintype n] (M N : Matrix n n QOmega) :
    cmat (M * N) = cmat M * cmat N := Matrix.map_mul

theorem cmat_one {n : Type*} [Fintype n] [DecidableEq n] :
    cmat (1 : Matrix n n QOmega) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- A matrix over ℚ(ω) with `M Mᴴ = 1`, as a complex unitary matrix. -/
noncomputable def unitaryQ {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n QOmega)
    (h : M * dagQ M = 1) : unitaryGroup n ℂ :=
  ⟨cmat M, by
    rw [mem_unitaryGroup_iff, star_cmat, ← cmat_mul, h, cmat_one]⟩

@[simp] theorem unitaryQ_val {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n QOmega)
    (h : M * dagQ M = 1) : (unitaryQ M h : Matrix n n ℂ) = cmat M := rfl

/-- The value of a word under generator matrices over ℚ(ω), read in `ℂ`. -/
theorem lift_unitaryQ {X : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (M : X → Matrix n n QOmega) (h : ∀ x, M x * dagQ (M x) = 1) (w : FreeMonoid X) :
    ((FreeMonoid.lift (fun x => unitaryQ (M x) (h x)) w : unitaryGroup n ℂ) : Matrix n n ℂ) =
      cmat (FreeMonoid.lift M w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp [cmat_one]
  | mul_of x w ih =>
    rw [map_mul, map_mul, Submonoid.coe_mul, ih, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, cmat_mul, unitaryQ_val]

/-- Two words with the same value over ℚ(ω) have the same complex unitary
value. -/
theorem lift_unitaryQ_eq {X : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (M : X → Matrix n n QOmega) (h : ∀ x, M x * dagQ (M x) = 1) {w v : FreeMonoid X}
    (hwv : FreeMonoid.lift M w = FreeMonoid.lift M v) :
    FreeMonoid.lift (fun x => unitaryQ (M x) (h x)) w =
      FreeMonoid.lift (fun x => unitaryQ (M x) (h x)) v := by
  apply Subtype.ext
  rw [lift_unitaryQ, lift_unitaryQ, hwv]

end QCert
