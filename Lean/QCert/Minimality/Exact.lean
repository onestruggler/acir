/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Integer quartic rings and the roots of unity of the six fragments

`ZQuartic p q` is ℤ[x]/(x⁴ - p x² - q), elements `a₀ + a₁ x + a₂ x² + a₃ x³`
with integer coefficients and decidable equality.  It is the integer
counterpart of the framework's `Quartic p q`, used because the kernel
evaluates integer arithmetic much faster than rational arithmetic.  The two
instances:

* `ZOmega = ZQuartic 0 (-1)`: ℤ[ω], ω = e^{iπ/4}, with `√2 = ω - ω³`;
* `ZZeta = ZQuartic 1 (-1)`: ℤ[ζ], ζ = e^{iπ/6}, with `√3 = 2ζ - ζ³`.

Matrices over these rings are the qubit and qutrit gate matrices scaled by
`√2` and `√3` (`QCert.Minimality.Scaled`).  `conj` is complex conjugation
(`x ↦ x⁻¹`), compatible with `star` on `ℂ` (`toC_conj`).
-/
import QCert.Exact.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace QCert.Minimality

/-- ℤ[x]/(x⁴ - p x² - q). -/
@[ext]
structure ZQuartic (p q : ℤ) where
  a0 : ℤ
  a1 : ℤ
  a2 : ℤ
  a3 : ℤ
  deriving DecidableEq

namespace ZQuartic

variable {p q : ℤ}

instance : Zero (ZQuartic p q) := ⟨⟨0, 0, 0, 0⟩⟩
instance : One (ZQuartic p q) := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add (ZQuartic p q) := ⟨fun a b => ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3⟩⟩
instance : Neg (ZQuartic p q) := ⟨fun a => ⟨-a.a0, -a.a1, -a.a2, -a.a3⟩⟩
instance : Sub (ZQuartic p q) := ⟨fun a b => ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩⟩

/-- Multiplication, reducing `x⁴ = p x² + q`, `x⁵ = p x³ + q x` and
`x⁶ = (p² + q) x² + p q`. -/
instance : Mul (ZQuartic p q) := ⟨fun a b =>
  let c4 := a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1
  let c5 := a.a2 * b.a3 + a.a3 * b.a2
  let c6 := a.a3 * b.a3
  ⟨a.a0 * b.a0 + q * c4 + p * q * c6,
   a.a0 * b.a1 + a.a1 * b.a0 + q * c5,
   a.a0 * b.a2 + a.a1 * b.a1 + a.a2 * b.a0 + p * c4 + (p * p + q) * c6,
   a.a0 * b.a3 + a.a1 * b.a2 + a.a2 * b.a1 + a.a3 * b.a0 + p * c5⟩⟩

theorem zero_def : (0 : ZQuartic p q) = ⟨0, 0, 0, 0⟩ := rfl
theorem one_def : (1 : ZQuartic p q) = ⟨1, 0, 0, 0⟩ := rfl
theorem add_def (a b : ZQuartic p q) :
    a + b = ⟨a.a0 + b.a0, a.a1 + b.a1, a.a2 + b.a2, a.a3 + b.a3⟩ := rfl
theorem neg_def (a : ZQuartic p q) : -a = ⟨-a.a0, -a.a1, -a.a2, -a.a3⟩ := rfl
theorem sub_def (a b : ZQuartic p q) :
    a - b = ⟨a.a0 - b.a0, a.a1 - b.a1, a.a2 - b.a2, a.a3 - b.a3⟩ := rfl
theorem mul_def (a b : ZQuartic p q) : a * b =
    ⟨a.a0 * b.a0 + q * (a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1) + p * q * (a.a3 * b.a3),
     a.a0 * b.a1 + a.a1 * b.a0 + q * (a.a2 * b.a3 + a.a3 * b.a2),
     a.a0 * b.a2 + a.a1 * b.a1 + a.a2 * b.a0 + p * (a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1) +
       (p * p + q) * (a.a3 * b.a3),
     a.a0 * b.a3 + a.a1 * b.a2 + a.a2 * b.a1 + a.a3 * b.a0 + p * (a.a2 * b.a3 + a.a3 * b.a2)⟩ :=
  rfl

attribute [local simp] zero_def one_def add_def neg_def sub_def mul_def in
instance : CommRing (ZQuartic p q) where
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
def X : ZQuartic p q := ⟨0, 1, 0, 0⟩

/-- An integer. -/
def ofInt (r : ℤ) : ZQuartic p q := ⟨r, 0, 0, 0⟩

theorem intCast_eq (r : ℤ) : ((r : ZQuartic p q)) = ofInt r := by
  induction r using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [Int.cast_add, Int.cast_one, ih]; ext <;> simp [ofInt, add_def, one_def]
  | pred k ih => rw [Int.cast_sub, Int.cast_one, ih]; ext <;> simp [ofInt, sub_def, one_def]

/-- Every element is `a₀ + a₁ x + a₂ x² + a₃ x³`. -/
theorem eq_sum (a : ZQuartic p q) :
    a = (a.a0 : ZQuartic p q) + (a.a1 : ZQuartic p q) * X + (a.a2 : ZQuartic p q) * X ^ 2 +
      (a.a3 : ZQuartic p q) * X ^ 3 := by
  simp only [intCast_eq, pow_succ, pow_zero]
  ext <;> simp [ofInt, X, add_def, mul_def, one_def]

section Lift

variable {R : Type*} [CommRing R]

/-- Evaluation at a root `θ` of `x⁴ = p x² + q` in any commutative ring. -/
def lift (θ : R) (hθ : θ ^ 4 = p * θ ^ 2 + q) : ZQuartic p q →+* R where
  toFun a := a.a0 + a.a1 * θ + a.a2 * θ ^ 2 + a.a3 * θ ^ 3
  map_one' := by simp [one_def]
  map_zero' := by simp [zero_def]
  map_add' a b := by simp [add_def]; ring
  map_mul' a b := by
    simp only [mul_def]
    push_cast
    linear_combination
      -((a.a1 * b.a3 + a.a2 * b.a2 + a.a3 * b.a1 : R) + (a.a2 * b.a3 + a.a3 * b.a2 : R) * θ +
        (a.a3 * b.a3 : R) * (θ ^ 2 + p)) * hθ

theorem lift_apply (θ : R) (hθ : θ ^ 4 = p * θ ^ 2 + q) (a : ZQuartic p q) :
    lift θ hθ a = a.a0 + a.a1 * θ + a.a2 * θ ^ 2 + a.a3 * θ ^ 3 := rfl

@[simp] theorem lift_X (θ : R) (hθ : θ ^ 4 = p * θ ^ 2 + q) : lift θ hθ X = θ := by
  simp [lift_apply, X]

/-- Two ring homomorphisms out of `ZQuartic p q` agreeing on `x` agree. -/
theorem hom_ext {f g : ZQuartic p q →+* R} (h : f X = g X) : f = g := by
  ext a
  rw [eq_sum a]
  simp only [map_add, map_mul, map_pow, map_intCast, h]

end Lift

end ZQuartic

/-- Integers in the framework's rational quartic ring. -/
theorem Quartic.intCast_eq' {p q : ℤ} (r : ℤ) : ((r : Quartic p q)) = ⟨r, 0, 0, 0⟩ := by
  induction r using Int.induction_on with
  | zero => rfl
  | succ k ih => rw [Int.cast_add, Int.cast_one, ih]; ext <;> simp
  | pred k ih => rw [Int.cast_sub, Int.cast_one, ih]; ext <;> simp

/-! ### ℤ[ω] -/

/-- ℤ[ω], ω⁴ = -1. -/
abbrev ZOmega := ZQuartic 0 (-1)

namespace ZOmega

open ZQuartic

/-- `√2 = ω - ω³`. -/
def sqrt2 : ZOmega := ⟨0, 1, 0, -1⟩

/-- `i = ω²`. -/
def I : ZOmega := ⟨0, 0, 1, 0⟩

/-- `ω`. -/
def ω : ZOmega := X

/-- ℤ[ω] inside `ℂ`, `x ↦ ω = e^{iπ/4}`. -/
noncomputable def toC : ZOmega →+* ℂ := lift QCert.ω (by rw [ω_pow_four]; push_cast; ring)

/-- ℤ[ω] inside ℚ(ω). -/
def toQ : ZOmega →+* QOmega := lift Quartic.X (by ext <;> simp [pow_succ, Quartic.X])

/-- Complex conjugation `ω ↦ ω⁻¹ = -ω³`. -/
def conj : ZOmega →+* ZOmega := lift ⟨0, 0, 0, -1⟩ (by decide)

theorem toC_X : toC X = QCert.ω := lift_X _ _

theorem toC_sqrt2 : toC sqrt2 = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h := QCert.inv_sqrt2_eq
  have h0 := QCert.sqrt2_ne_zero
  have h2 := QCert.sqrt2_sq
  have e : toC sqrt2 = QCert.ω - QCert.ω ^ 3 := by
    simp only [toC, lift_apply, sqrt2]; push_cast; ring
  rw [e, show QCert.ω - QCert.ω ^ 3 = 2 * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ by rw [h]; ring]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by rw [← sq, h2]
  rw [← hs, mul_assoc, mul_inv_cancel₀ h0, mul_one]

theorem toC_I : toC I = Complex.I := by
  simp only [toC, lift_apply, I]
  push_cast
  rw [QCert.ω_sq]; ring

theorem star_ω : star QCert.ω = -QCert.ω ^ 3 := by
  have h3 : QCert.ω ^ 3 = QCert.ω * Complex.I := by rw [pow_succ, QCert.ω_sq, mul_comm]
  rw [h3]
  simp only [QCert.ω, star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal, map_add,
    map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `conj` is complex conjugation. -/
theorem toC_conj (a : ZOmega) : toC (conj a) = star (toC a) := by
  have : toC.comp conj = (starRingEnd ℂ).comp toC := by
    apply hom_ext
    simp only [RingHom.comp_apply, conj, lift_X, starRingEnd_apply]
    rw [toC_X, star_ω]
    simp [toC, lift_apply]
  exact congrArg (fun f : ZOmega →+* ℂ => f a) this

theorem toQ_apply (a : ZOmega) : toQ a = ⟨a.a0, a.a1, a.a2, a.a3⟩ := by
  simp only [toQ, lift_apply, Quartic.intCast_eq']
  ext <;> simp [Quartic.X, pow_succ]

theorem toQ_injective : Function.Injective toQ := by
  intro a b h
  rw [toQ_apply, toQ_apply] at h
  simp only [Quartic.mk.injEq, Int.cast_inj] at h
  ext <;> simp [h]

theorem isUnit_toQ_sqrt2 : IsUnit (toQ sqrt2) := by
  refine IsUnit.of_mul_eq_one QOmega.invSqrt2 ?_
  rw [toQ_apply]
  ext <;> simp [sqrt2, QOmega.invSqrt2] <;> norm_num

theorem isUnit_toQ_ω_pow (k : ℕ) : IsUnit (toQ (ω ^ k)) := by
  refine IsUnit.of_mul_eq_one (toQ (ω ^ (8 * k - k))) ?_
  rw [← map_mul, ← pow_add, show k + (8 * k - k) = 8 * k by omega, pow_mul,
    show ω ^ 8 = (1 : ZOmega) by decide, one_pow, map_one]

end ZOmega

/-! ### ℤ[ζ₁₂] -/

/-- ℤ[ζ], ζ = ζ₁₂ = e^{iπ/6}, ζ⁴ = ζ² - 1. -/
abbrev ZZeta := ZQuartic 1 (-1)

namespace ZZeta

open ZQuartic

/-- `ζ₁₂ = (√3 + i)/2 = e^{iπ/6}` (`ζ12_eq_exp`). -/
noncomputable def ζ12 : ℂ := (((Real.sqrt 3 : ℝ) : ℂ) + Complex.I) / 2

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem sqrt3_ne_zero : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
  intro h; have := sqrt3_sq; rw [h] at this; norm_num at this

theorem ζ12_eq_exp : ζ12 = Complex.exp (↑(Real.pi / 6) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_six,
    Real.sin_pi_div_six, ζ12]
  push_cast; ring

theorem ζ12_pow_four : ζ12 ^ 4 = ((1 : ℤ) : ℂ) * ζ12 ^ 2 + ((-1 : ℤ) : ℂ) := by
  have h3 := sqrt3_sq
  have hI := Complex.I_sq
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
  simp only [ζ12, Int.cast_one, Int.cast_neg]
  linear_combination ((6 * Complex.I ^ 2 + 4 * Complex.I * s + s ^ 2 - 1) / 16) * h3 +
    ((Complex.I ^ 2 + 4 * Complex.I * s + 13) / 16) * hI

theorem ζ12_pow_three : ζ12 ^ 3 = Complex.I := by
  have h3 := sqrt3_sq
  have hI := Complex.I_sq
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
  simp only [ζ12]
  linear_combination ((3 * Complex.I + s) / 8) * h3 + ((Complex.I + 3 * s) / 8) * hI

/-- ℤ[ζ] inside `ℂ`, `x ↦ ζ₁₂`. -/
noncomputable def toC : ZZeta →+* ℂ := lift ζ12 ζ12_pow_four

/-- `ζ`. -/
def ζ : ZZeta := X

/-- `√3 = 2ζ - ζ³`. -/
def sqrt3 : ZZeta := ⟨0, 2, 0, -1⟩

/-- Complex conjugation `ζ ↦ ζ⁻¹ = ζ - ζ³`. -/
def conj : ZZeta →+* ZZeta := lift ⟨0, 1, 0, -1⟩ (by decide)

/-- ℤ[ζ] inside ℚ(ζ₁₂). -/
def toQ : ZZeta →+* Quartic 1 (-1) := lift Quartic.X (by ext <;> simp [pow_succ, Quartic.X])

theorem toC_X : toC X = ζ12 := lift_X _ _

theorem toC_sqrt3 : toC sqrt3 = ((Real.sqrt 3 : ℝ) : ℂ) := by
  have e : toC sqrt3 = 2 * ζ12 - ζ12 ^ 3 := by
    simp only [toC, lift_apply, sqrt3]; push_cast; ring
  rw [e, ζ12_pow_three, ζ12]; ring

theorem star_ζ12 : star ζ12 = ζ12 - ζ12 ^ 3 := by
  rw [ζ12_pow_three]
  simp only [ζ12, star_div₀, star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  ring

/-- `conj` is complex conjugation. -/
theorem toC_conj (a : ZZeta) : toC (conj a) = star (toC a) := by
  have : toC.comp conj = (starRingEnd ℂ).comp toC := by
    apply hom_ext
    simp only [RingHom.comp_apply, conj, lift_X, starRingEnd_apply]
    rw [toC_X, star_ζ12]
    simp [toC, lift_apply]
    ring
  exact congrArg (fun f : ZZeta →+* ℂ => f a) this

theorem toQ_apply (a : ZZeta) : toQ a = ⟨a.a0, a.a1, a.a2, a.a3⟩ := by
  simp only [toQ, lift_apply, Quartic.intCast_eq']
  ext <;> simp [Quartic.X, pow_succ]

theorem toQ_injective : Function.Injective toQ := by
  intro a b h
  rw [toQ_apply, toQ_apply] at h
  simp only [Quartic.mk.injEq, Int.cast_inj] at h
  ext <;> simp [h]

theorem isUnit_toQ_sqrt3 : IsUnit (toQ sqrt3) := by
  refine IsUnit.of_mul_eq_one (⟨0, 2 / 3, 0, -1 / 3⟩ : Quartic 1 (-1)) ?_
  rw [toQ_apply]
  ext <;> simp [sqrt3] <;> norm_num

theorem isUnit_toQ_ζ_pow (k : ℕ) : IsUnit (toQ (ζ ^ k)) := by
  refine IsUnit.of_mul_eq_one (toQ (ζ ^ (12 * k - k))) ?_
  rw [← map_mul, ← pow_add, show k + (12 * k - k) = 12 * k by omega, pow_mul,
    show ζ ^ 12 = (1 : ZZeta) by decide, one_pow, map_one]

end ZZeta

end QCert.Minimality
