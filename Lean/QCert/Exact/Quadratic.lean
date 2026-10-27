/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A computable quadratic number ring

`Quadratic d` is ℚ[x]/(x² - d), elements `a₀ + a₁ x` with rational
coefficients and decidable equality.  For a non-square `d` it is the field
ℚ(√d), and an identity holds in it exactly when it holds after `lift`.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Rat.Cast.CharZero

namespace QCert

/-- ℚ[x]/(x² - d). -/
@[ext]
structure Quadratic (d : ℤ) where
  a0 : ℚ
  a1 : ℚ
  deriving DecidableEq

namespace Quadratic

variable {d : ℤ}

instance : Zero (Quadratic d) := ⟨⟨0, 0⟩⟩
instance : One (Quadratic d) := ⟨⟨1, 0⟩⟩
instance : Add (Quadratic d) := ⟨fun a b => ⟨a.a0 + b.a0, a.a1 + b.a1⟩⟩
instance : Neg (Quadratic d) := ⟨fun a => ⟨-a.a0, -a.a1⟩⟩
instance : Sub (Quadratic d) := ⟨fun a b => ⟨a.a0 - b.a0, a.a1 - b.a1⟩⟩
instance : Mul (Quadratic d) :=
  ⟨fun a b => ⟨a.a0 * b.a0 + d * (a.a1 * b.a1), a.a0 * b.a1 + a.a1 * b.a0⟩⟩

@[simp] theorem zero_def : (0 : Quadratic d) = ⟨0, 0⟩ := rfl
@[simp] theorem one_def : (1 : Quadratic d) = ⟨1, 0⟩ := rfl
@[simp] theorem add_def (a b : Quadratic d) : a + b = ⟨a.a0 + b.a0, a.a1 + b.a1⟩ := rfl
@[simp] theorem neg_def (a : Quadratic d) : -a = ⟨-a.a0, -a.a1⟩ := rfl
@[simp] theorem sub_def (a b : Quadratic d) : a - b = ⟨a.a0 - b.a0, a.a1 - b.a1⟩ := rfl
@[simp] theorem mul_def (a b : Quadratic d) :
    a * b = ⟨a.a0 * b.a0 + d * (a.a1 * b.a1), a.a0 * b.a1 + a.a1 * b.a0⟩ := rfl

instance : CommRing (Quadratic d) where
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

/-- The element `x`, a square root of `d`. -/
def X : Quadratic d := ⟨0, 1⟩

/-- A rational number. -/
def ofRat (r : ℚ) : Quadratic d := ⟨r, 0⟩

section Lift

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluation at a square root `θ` of `d`. -/
def lift (θ : K) (hθ : θ ^ 2 = d) : Quadratic d →+* K where
  toFun a := a.a0 + a.a1 * θ
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp; ring
  map_mul' a b := by
    simp only [mul_def]
    push_cast
    linear_combination (-(a.a1 * b.a1 : K)) * hθ

theorem lift_apply (θ : K) (hθ : θ ^ 2 = d) (a : Quadratic d) :
    lift θ hθ a = a.a0 + a.a1 * θ := rfl

@[simp] theorem lift_X (θ : K) (hθ : θ ^ 2 = d) : lift θ hθ X = θ := by
  simp [lift_apply, X]

@[simp] theorem lift_ofRat (θ : K) (hθ : θ ^ 2 = d) (r : ℚ) : lift θ hθ (ofRat r) = r := by
  simp [lift_apply, ofRat]

end Lift

end Quadratic

end QCert
