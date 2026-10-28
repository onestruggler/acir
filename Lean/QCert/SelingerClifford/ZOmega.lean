/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The ring ℤ[ω]

`ZOmega` is ℤ[x]/(x⁴ + 1), elements `a₀ + a₁ ω + a₂ ω² + a₃ ω³` with integer
coefficients and decidable equality.  Its arithmetic is integer arithmetic,
which the kernel evaluates much faster than the rational arithmetic of
`QOmega`; `toC` sends `x` to `ω = e^{iπ/4}`, and `√2 = ω - ω³` and
`i = ω²` lie in it.
-/
import QCert.Exact.Roots

namespace QCert.SelingerClifford

/-- ℤ[ω] = ℤ[x]/(x⁴ + 1). -/
@[ext]
structure ZOmega where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  deriving DecidableEq

namespace ZOmega

instance : Zero ZOmega := ⟨⟨0, 0, 0, 0⟩⟩
instance : One ZOmega := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add ZOmega := ⟨fun a b => ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3⟩⟩
instance : Neg ZOmega := ⟨fun a => ⟨-a.a0, -a.a1, -a.a2, -a.a3⟩⟩
instance : Sub ZOmega := ⟨fun a b => ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩⟩

/-- Multiplication, reducing `x⁴ = -1`. -/
instance : Mul ZOmega := ⟨fun a b =>
  ⟨a.a0 * b.a0 - a.a1 * b.a3 - a.a2 * b.a2 - a.a3 * b.a1,
   a.a0 * b.a1 + a.a1 * b.a0 - a.a2 * b.a3 - a.a3 * b.a2,
   a.a0 * b.a2 + a.a1 * b.a1 + a.a2 * b.a0 - a.a3 * b.a3,
   a.a0 * b.a3 + a.a1 * b.a2 + a.a2 * b.a1 + a.a3 * b.a0⟩⟩

@[simp] theorem zero_def : (0 : ZOmega) = ⟨0, 0, 0, 0⟩ := rfl
@[simp] theorem one_def : (1 : ZOmega) = ⟨1, 0, 0, 0⟩ := rfl
@[simp] theorem add_def (a b : ZOmega) :
    a + b = ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3⟩ := rfl
@[simp] theorem neg_def (a : ZOmega) : -a = ⟨-a.a0, -a.a1, -a.a2, -a.a3⟩ := rfl
@[simp] theorem sub_def (a b : ZOmega) :
    a - b = ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩ := rfl
@[simp] theorem mul_def (a b : ZOmega) : a * b =
    ⟨a.a0 * b.a0 - a.a1 * b.a3 - a.a2 * b.a2 - a.a3 * b.a1,
     a.a0 * b.a1 + a.a1 * b.a0 - a.a2 * b.a3 - a.a3 * b.a2,
     a.a0 * b.a2 + a.a1 * b.a1 + a.a2 * b.a0 - a.a3 * b.a3,
     a.a0 * b.a3 + a.a1 * b.a2 + a.a2 * b.a1 + a.a3 * b.a0⟩ := rfl

instance : CommRing ZOmega where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp <;> ring
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- `ω`. -/
def X : ZOmega := ⟨0, 1, 0, 0⟩
/-- `i = ω²`. -/
def I : ZOmega := ⟨0, 0, 1, 0⟩
/-- `√2 = ω - ω³`. -/
def sqrt2 : ZOmega := ⟨0, 1, 0, -1⟩

/-- ℤ[ω] inside ℚ(ω). -/
def toQ : ZOmega →+* QOmega where
  toFun a := ⟨a.a0, a.a1, a.a2, a.a3⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp <;> ring

/-- ℤ[ω] inside `ℂ`, `x ↦ ω`. -/
noncomputable def toC : ZOmega →+* ℂ := QOmega.toC.comp toQ

theorem toC_apply (a : ZOmega) :
    toC a = a.a0 + a.a1 * ω + a.a2 * ω ^ 2 + a.a3 * ω ^ 3 := by
  simp [toC, toQ, QOmega.toC, Quartic.lift_apply]

theorem toC_X : toC X = ω := by simp [toC_apply, X]

theorem toC_I : toC I = Complex.I := by simp [toC_apply, I, ω_sq]

theorem toC_sqrt2 : toC sqrt2 = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h := inv_sqrt2_eq
  have h0 := sqrt2_ne_zero
  have h2 := sqrt2_sq
  rw [toC_apply]
  simp only [sqrt2, Int.cast_zero, Int.cast_one, Int.cast_neg, zero_mul, one_mul, zero_add,
    add_zero, neg_mul]
  have : ω - ω ^ 3 = 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by rw [h]; ring
  rw [← sub_eq_add_neg, this]
  field_simp
  rw [h2]

end ZOmega

end QCert.SelingerClifford
