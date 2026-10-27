/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Roots of unity and √2 as quartic numbers

* `ω = (1 + i)/√2 = e^{iπ/4}`, with `QOmega = Quartic 0 (-1)` and
  `QOmega.toC : QOmega →+* ℂ` sending `x` to `ω`;
* `ζ₁₂ = e^{iπ/6}`, with `QZeta12 = Quartic 1 (-1)` and `QZeta12.toC`;
* `√2 ∈ ℝ`, with `QSqrt2 = Quartic 2 0` and `QSqrt2.toR` sending `x` to `√2`.
-/
import QCert.Exact.Quartic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace QCert

open Complex

noncomputable section

/-- `ω = (1 + i)/√2`, the primitive eighth root of unity `e^{iπ/4}`. -/
def ω : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (1 + I)

theorem sqrt2_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem sqrt2_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  intro h; have := sqrt2_sq; rw [h] at this; norm_num at this

theorem ω_sq : ω ^ 2 = I := by
  rw [ω, mul_pow, inv_pow, sqrt2_sq]
  have : (1 + I) ^ 2 = 2 * I := by ring_nf; rw [I_sq]; ring
  rw [this]; field_simp

theorem ω_pow_four : ω ^ 4 = -1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ω_sq, I_sq]

/-- `1/√2 = (ω - ω³)/2`. -/
theorem inv_sqrt2_eq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (ω - ω ^ 3) / 2 := by
  have h3 : ω ^ 3 = ω * I := by rw [pow_succ, ω_sq, mul_comm]
  rw [h3, ω]
  field_simp
  ring_nf
  rw [I_sq]
  norm_num

/-- ℚ(ω), ω⁴ = -1. -/
abbrev QOmega := Quartic 0 (-1)

/-- ℚ(ω) inside `ℂ`. -/
def QOmega.toC : QOmega →+* ℂ := Quartic.lift ω (by rw [ω_pow_four]; push_cast; ring)

/-- `1/√2 ∈ ℚ(ω)`. -/
def QOmega.invSqrt2 : QOmega := ⟨0, 1 / 2, 0, -1 / 2⟩

/-- `i ∈ ℚ(ω)`. -/
def QOmega.I : QOmega := ⟨0, 0, 1, 0⟩

theorem QOmega.toC_invSqrt2 : QOmega.toC QOmega.invSqrt2 = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [inv_sqrt2_eq]
  simp only [QOmega.toC, Quartic.lift_apply, QOmega.invSqrt2]
  push_cast; ring

theorem QOmega.toC_I : QOmega.toC QOmega.I = Complex.I := by
  simp only [QOmega.toC, Quartic.lift_apply, QOmega.I]
  push_cast; rw [ω_sq]; ring

theorem QOmega.toC_X : QOmega.toC Quartic.X = ω := Quartic.lift_X _ _

/-- `√2 ∈ ℝ` as a root of `x⁴ = 2 x²`. -/
abbrev QSqrt2 := Quartic 2 0

/-- `QSqrt2` onto ℚ(√2) ⊆ ℝ. -/
def QSqrt2.toR : QSqrt2 →+* ℝ :=
  Quartic.lift (Real.sqrt 2) (by
    have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h]; push_cast; ring)

/-- `1/√2 = √2/2 ∈ QSqrt2`. -/
def QSqrt2.invSqrt2 : QSqrt2 := ⟨0, 1 / 2, 0, 0⟩

theorem QSqrt2.toR_invSqrt2 : QSqrt2.toR QSqrt2.invSqrt2 = (Real.sqrt 2)⁻¹ := by
  simp only [QSqrt2.toR, Quartic.lift_apply, QSqrt2.invSqrt2]
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  push_cast
  nlinarith [h]

end

end QCert
