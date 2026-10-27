/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Exact rings and the matrix groups over them

The rings of exact synthesis, as subrings of `ℂ` and `ℝ`:

* `ZInvSqrt2I`: ℤ[1/√2, i] (also written 𝔻[ω], ω = e^{iπ/4}),
* `ZHalfI`: ℤ[1/2, i],
* `ZInvSqrt2`: ℤ[1/√2] (real),
* `ZHalf`: ℤ[1/2] (real, the dyadic rationals 𝔻).

For a subring `S` closed under the involution, `unitaryOver ι S` is the
group of unitary matrices with entries in `S`: `Uₙ(S)` for a subring of `ℂ`
and `Oₙ(S)` for a subring of `ℝ`, whose involution is trivial.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Subring.Basic

namespace QCert

open Matrix

noncomputable section

/-- ℤ[1/√2, i] ⊆ ℂ. -/
def ZInvSqrt2I : Subring ℂ := Subring.closure {((Real.sqrt 2 : ℝ) : ℂ)⁻¹, Complex.I}

/-- ℤ[1/2, i] ⊆ ℂ. -/
def ZHalfI : Subring ℂ := Subring.closure {(2 : ℂ)⁻¹, Complex.I}

/-- ℤ[1/√2] ⊆ ℝ. -/
def ZInvSqrt2 : Subring ℝ := Subring.closure {(Real.sqrt 2)⁻¹}

/-- ℤ[1/2] ⊆ ℝ, the dyadic rationals. -/
def ZHalf : Subring ℝ := Subring.closure {(2 : ℝ)⁻¹}

/-- A subring closed under the involution. -/
def StarClosed {K : Type*} [Ring K] [StarRing K] (S : Subring K) : Prop :=
  ∀ x ∈ S, star x ∈ S

theorem starClosed_of_trivialStar {K : Type*} [Ring K] [StarRing K] [TrivialStar K]
    (S : Subring K) : StarClosed S := fun x hx => by rwa [star_trivial]

/-- The closure of a set whose conjugates lie in the closure is closed under
conjugation. -/
theorem starClosed_closure {K : Type*} [CommRing K] [StarRing K] {s : Set K}
    (h : ∀ x ∈ s, star x ∈ Subring.closure s) : StarClosed (Subring.closure s) := by
  intro x hx
  have : Subring.closure s ≤ (Subring.closure s).comap (starRingEnd K) :=
    Subring.closure_le.2 fun y hy => h y hy
  exact this hx

theorem starClosed_ZInvSqrt2I : StarClosed ZInvSqrt2I := by
  apply starClosed_closure
  rintro x (rfl | rfl)
  · apply Subring.subset_closure
    left
    simp [Complex.conj_ofReal]
  · have : star Complex.I = -Complex.I := Complex.conj_I
    rw [this]
    exact Subring.neg_mem _ (Subring.subset_closure (by simp))

theorem starClosed_ZHalfI : StarClosed ZHalfI := by
  apply starClosed_closure
  rintro x (rfl | rfl)
  · apply Subring.subset_closure
    left
    simp
  · have : star Complex.I = -Complex.I := Complex.conj_I
    rw [this]
    exact Subring.neg_mem _ (Subring.subset_closure (by simp))

/-- The unitary matrices with entries in a subring `S` closed under the
involution: `Uₙ(S)` over `ℂ`, `Oₙ(S)` over `ℝ`. -/
def unitaryOver {K : Type*} [CommRing K] [StarRing K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (S : Subring K) (hS : StarClosed S) : Subgroup (unitaryGroup ι K) where
  carrier := {U | ∀ i j, (U : Matrix ι ι K) i j ∈ S}
  mul_mem' {U V} hU hV i j := by
    show (U.1 * V.1) i j ∈ S
    rw [mul_apply]
    exact Subring.sum_mem _ fun k _ => S.mul_mem (hU i k) (hV k j)
  one_mem' i j := by
    show (1 : Matrix ι ι K) i j ∈ S
    rw [one_apply]; split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  inv_mem' {U} hU i j := by
    show (star U.1) i j ∈ S
    rw [star_apply]
    exact hS _ (hU j i)

theorem mem_unitaryOver {K : Type*} [CommRing K] [StarRing K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Subring K} {hS : StarClosed S} {U : unitaryGroup ι K} :
    U ∈ unitaryOver ι S hS ↔ ∀ i j, (U : Matrix ι ι K) i j ∈ S := Iff.rfl

/-- `Uₙ(ℤ[1/√2, i])`. -/
abbrev U_ZInvSqrt2I (n : ℕ) : Subgroup (unitaryGroup (Fin n) ℂ) :=
  unitaryOver (Fin n) ZInvSqrt2I starClosed_ZInvSqrt2I

/-- `Uₙ(ℤ[1/2, i])`. -/
abbrev U_ZHalfI (n : ℕ) : Subgroup (unitaryGroup (Fin n) ℂ) :=
  unitaryOver (Fin n) ZHalfI starClosed_ZHalfI

/-- `Oₙ(ℤ[1/√2])`. -/
abbrev O_ZInvSqrt2 (n : ℕ) : Subgroup (unitaryGroup (Fin n) ℝ) :=
  unitaryOver (Fin n) ZInvSqrt2 (starClosed_of_trivialStar _)

/-- `Oₙ(ℤ[1/2])`. -/
abbrev O_ZHalf (n : ℕ) : Subgroup (unitaryGroup (Fin n) ℝ) :=
  unitaryOver (Fin n) ZHalf (starClosed_of_trivialStar _)

end

end QCert
