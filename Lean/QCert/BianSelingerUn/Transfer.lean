/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Identities of level matrices, from a computation over `ℚ(ω)`

A relation between products of one- and two-level matrices on `m` distinct
symbolic indices `φ 0, …, φ (m - 1)` is the image under
`T φ = levelMat φ ∘ (·).map QOmega.toC` of the same relation on the indices
`0, …, m - 1` over the computable field `ℚ(ω)` (`QOmega`), where it is
decided by `decide +kernel`.
-/
import QCert.BianSelingerUn.LevelCalc
import QCert.Exact.Roots

namespace QCert

open Matrix

noncomputable section

variable {n m : ℕ}

/-- `levelMat φ` after reading a matrix over `ℚ(ω)` in `ℂ`. -/
def transferHom {φ : Fin m → Fin n} (hφ : Function.Injective φ) :
    Matrix (Fin m) (Fin m) QOmega →* Matrix (Fin n) (Fin n) ℂ :=
  (levelHom hφ).comp (RingHom.mapMatrix QOmega.toC).toMonoidHom

@[simp] theorem transferHom_twoLevel {φ : Fin m → Fin n} (hφ : Function.Injective φ)
    (a b : Fin m) (U : Matrix (Fin 2) (Fin 2) QOmega) :
    transferHom hφ (twoLevel a b U) = twoLevel (φ a) (φ b) (U.map QOmega.toC) := by
  simp only [transferHom, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, levelHom_apply, twoLevel_map, levelMat_twoLevel]

@[simp] theorem transferHom_oneLevel {φ : Fin m → Fin n} (hφ : Function.Injective φ)
    (a : Fin m) (z : QOmega) :
    transferHom hφ (oneLevel a z) = oneLevel (φ a) (QOmega.toC z) := by
  simp only [transferHom, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, levelHom_apply, oneLevel_map, levelMat_oneLevel]

end

variable {n : ℕ}

theorem injective_three {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

theorem injective_four {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

end QCert
