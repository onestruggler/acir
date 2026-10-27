/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A computable quartic number ring

`Quartic p q` is ℚ[x]/(x⁴ - p x² - q), elements `a₀ + a₁ x + a₂ x² + a₃ x³`
with rational coefficients and decidable equality, so that identities
between matrices over it are decided by `decide +kernel`.  For any root
`θ` of `x⁴ = p x² + q` in a field of characteristic zero, `Quartic.lift θ`
is a ring homomorphism.  The instances used in the corpus:

* `p = 0, q = -1`: ℚ(ω), ω = e^{iπ/4}, which holds ℤ[1/√2, i] and ℤ[1/2, i];
* `p = 1, q = -1`: ℚ(ζ₁₂).

Both polynomials are irreducible over ℚ, so these rings are fields and an
identity holds in them exactly when it holds in `ℂ`.  For any other `(p, q)`
check irreducibility before relying on it: ℚ[x]/(x⁴ - 2x²) is not ℚ(√2)
(there `x² ≠ 2`); ℚ(√2) is `Quadratic 2`.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Rat.Cast.CharZero

namespace QCert

/-- ℚ[x]/(x⁴ - p x² - q). -/
@[ext]
structure Quartic (p q : ℤ) where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  deriving DecidableEq

namespace Quartic

variable {p q : ℤ}

instance : Zero (Quartic p q) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (Quartic p q) := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add (Quartic p q) := ⟨fun a b => ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3⟩⟩
instance : Neg (Quartic p q) := ⟨fun a => ⟨-a.a0, -a.a1, -a.a2, -a.a3⟩⟩
instance : Sub (Quartic p q) := ⟨fun a b => ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩⟩

/-- Multiplication, reducing `x⁴ = p x² + q`, `x⁵ = p x³ + q x` and
`x⁶ = (p² + q) x² + p q`. -/
instance : Mul (Quartic p q) := ⟨fun a b =>
  let c4 := a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1
  let c5 := a.a2 * b.a3 + a.a3 * b.a2
  let c6 := a.a3 * b.a3
  ⟨a.a0 * b.a0 + q * c4 + p * q * c6,
   a.a0 * b.a1 + a.a1 * b.a0 + q * c5,
   a.a0 * b.a2 + a.a1 * b.a1 + a.a2 * b.a0 + p * c4 + (p * p + q) * c6,
   a.a0 * b.a3 + a.a1 * b.a2 + a.a2 * b.a1 + a.a3 * b.a0 + p * c5⟩⟩

@[simp] theorem zero_def : (0 : Quartic p q) = ⟨0, 0, 0, 0⟩ := rfl
@[simp] theorem one_def : (1 : Quartic p q) = ⟨1, 0, 0, 0⟩ := rfl
@[simp] theorem add_def (a b : Quartic p q) :
    a + b = ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3⟩ := rfl
@[simp] theorem neg_def (a : Quartic p q) : -a = ⟨-a.a0, -a.a1, -a.a2, -a.a3⟩ := rfl
@[simp] theorem sub_def (a b : Quartic p q) :
    a - b = ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩ := rfl
@[simp] theorem mul_def (a b : Quartic p q) : a * b =
    ⟨a.a0 * b.a0 + q * (a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1) + p * q * (a.a3 * b.a3),
     a.a0 * b.a1 + a.a1 * b.a0 + q * (a.a2 * b.a3 + a.a3 * b.a2),
     a.a0 * b.a2 + a.a1 * b.a1 + a.a2 * b.a0 + p * (a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1) +
       (p * p + q) * (a.a3 * b.a3),
     a.a0 * b.a3 + a.a1 * b.a2 + a.a2 * b.a1 + a.a3 * b.a0 + p * (a.a2 * b.a3 + a.a3 * b.a2)⟩ :=
  rfl

instance : CommRing (Quartic p q) where
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

/-- The element `x`. -/
def X : Quartic p q := ⟨0, 1, 0, 0⟩

/-- A rational number. -/
def ofRat (r : ℚ) : Quartic p q := ⟨r, 0, 0, 0⟩

section Lift

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluation at a root `θ` of `x⁴ = p x² + q`. -/
def lift (θ : K) (hθ : θ ^ 4 = p * θ ^ 2 + q) : Quartic p q →+* K where
  toFun a := a.a0 + a.a1 * θ + a.a2 * θ ^ 2 + a.a3 * θ ^ 3
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp; ring
  map_mul' a b := by
    simp only [mul_def]
    push_cast
    linear_combination
      -((a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1 : K) + (a.a2 * b.a3 + a.a3 * b.a2 : K) * θ +
        (a.a3 * b.a3 : K) * (θ ^ 2 + p)) * hθ

theorem lift_apply (θ : K) (hθ : θ ^ 4 = p * θ ^ 2 + q) (a : Quartic p q) :
    lift θ hθ a = a.a0 + a.a1 * θ + a.a2 * θ ^ 2 + a.a3 * θ ^ 3 := rfl

@[simp] theorem lift_X (θ : K) (hθ : θ ^ 4 = p * θ ^ 2 + q) : lift θ hθ X = θ := by
  simp [lift_apply, X]

@[simp] theorem lift_ofRat (θ : K) (hθ : θ ^ 4 = p * θ ^ 2 + q) (r : ℚ) :
    lift θ hθ (ofRat r) = r := by
  simp [lift_apply, ofRat]

end Lift

end Quartic

end QCert
