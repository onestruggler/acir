/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three-qubit Clifford+CS: soundness of the relations of Figure 2

Every relation of Figure 2 holds in `U(8)`: each instance is decided by
`check` (`Eval.lean`).  Every generator has an inverse modulo the
relations (`grouplike`).
-/
import QCert.CliffordCS3.Eval
import QCert.CliffordT2.Derivation
import Mathlib.Tactic.FinCases

namespace QCert.CliffordCS3

open W

/-- Every relation instance is decided sound. -/
theorem rel_check : ∀ {w v : Word Gen}, Rel w v → check w v = true := by
  intro w v h
  cases h with
  | c1 => decide +kernel
  | c2 q => fin_cases q <;> decide +kernel
  | c3 q => fin_cases q <;> decide +kernel
  | c4 q => fin_cases q <;> decide +kernel
  | c5 j => fin_cases j <;> decide +kernel
  | c6 j => fin_cases j <;> decide +kernel
  | c7 j => fin_cases j <;> decide +kernel
  | c8 j => fin_cases j <;> decide +kernel
  | c9 j => fin_cases j <;> decide +kernel
  | c10 j => fin_cases j <;> decide +kernel
  | c11 j => fin_cases j <;> decide +kernel
  | c12 => decide +kernel
  | c13 => decide +kernel
  | c14 => decide +kernel
  | c15 => decide +kernel
  | c16 => decide +kernel
  | c17 => decide +kernel
  | comm_i A hA => cases A <;> first | exact absurd rfl hA | decide +kernel
  | comm_loc A B q r hqr =>
    cases A <;> cases B <;> fin_cases q <;> fin_cases r <;>
      first | exact absurd hqr (by decide) | decide +kernel
  | comm_0_12 A => cases A <;> decide +kernel
  | comm_2_01 A => cases A <;> decide +kernel

/-- Soundness: every relation of Figure 2 holds in `U(8)`. -/
theorem sound : ∀ ⦃w v : Word Gen⦄, Rel w v → FreeMonoid.lift sem w = FreeMonoid.lift sem v :=
  fun _ _ h => sem_eq_of_check (rel_check h)

/-- `K_q i K_q = ε`, from (C2) and (C1). -/
theorem K_inv (q : Fin 3) : Derivable Rel (I * K q * K q) 1 := by
  have h : I * K q * K q = I * K q ^ 2 := by rw [mul_assoc, ← sq]
  rw [h]
  have h2 : I * I ^ 3 = I ^ 4 := by rw [← pow_succ']
  exact ((Derivable.of (Rel.c2 q)).mul_left I).trans (h2 ▸ Derivable.of Rel.c1)

/-- Every generator has a left inverse modulo the relations. -/
theorem grouplike : Grouplike Rel := by
  intro x
  cases x with
  | i => exact ⟨I ^ 3, (pow_succ I 3).symm ▸ Derivable.of Rel.c1⟩
  | K₀ => exact ⟨I * K 0, K_inv 0⟩
  | K₁ => exact ⟨I * K 1, K_inv 1⟩
  | K₂ => exact ⟨I * K 2, K_inv 2⟩
  | S₀ => exact ⟨S 0 ^ 3, (pow_succ (S 0) 3).symm ▸ Derivable.of (Rel.c3 0)⟩
  | S₁ => exact ⟨S 1 ^ 3, (pow_succ (S 1) 3).symm ▸ Derivable.of (Rel.c3 1)⟩
  | S₂ => exact ⟨S 2 ^ 3, (pow_succ (S 2) 3).symm ▸ Derivable.of (Rel.c3 2)⟩
  | CS₀₁ => exact ⟨CS 0 ^ 3, (pow_succ (CS 0) 3).symm ▸ Derivable.of (Rel.c5 0)⟩
  | CS₁₂ => exact ⟨CS 1 ^ 3, (pow_succ (CS 1) 3).symm ▸ Derivable.of (Rel.c5 1)⟩

end QCert.CliffordCS3
