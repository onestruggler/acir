/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two-qubit Clifford+T: soundness of the relations of Figure 1

Every relation (C1)–(C20) holds in `U(4)`: each instance is decided by
`check` (`Eval.lean`).  Every generator has an inverse modulo the
relations (`grouplike`).
-/
import QCert.CliffordT2.Eval
import QCert.CliffordT2.Derivation

namespace QCert.CliffordT2

open W

/-- Every relation instance is decided sound. -/
theorem rel_check : ∀ {w v : Word Gen}, Rel w v → check w v = true := by
  intro w v h
  cases h with
  | c1 A hA => cases A <;> first | exact absurd rfl hA | decide +kernel
  | c2 A B => cases A <;> cases B <;> decide +kernel
  | c3 => decide +kernel
  | c4 i => fin_cases i <;> decide +kernel
  | c5 i => fin_cases i <;> decide +kernel
  | c6 i => fin_cases i <;> decide +kernel
  | c7 => decide +kernel
  | c8 => decide +kernel
  | c9 => decide +kernel
  | c10 => decide +kernel
  | c11 => decide +kernel
  | c12 => decide +kernel
  | c13 => decide +kernel
  | c14 i => fin_cases i <;> decide +kernel
  | c15 i => fin_cases i <;> decide +kernel
  | c16 => decide +kernel
  | c17 => decide +kernel
  | c18 => decide +kernel
  | c19 => decide +kernel
  | c20 => decide +kernel

/-- Soundness: every relation of Figure 1 holds in `U(4)`. -/
theorem sound : ∀ ⦃w v : Word Gen⦄, Rel w v → FreeMonoid.lift sem w = FreeMonoid.lift sem v :=
  fun _ _ h => sem_eq_of_check (rel_check h)

/-- `Tᵢ⁸ = ε`, from (C14) and (C5). -/
theorem T_pow_eight (i : Fin 2) : Derivable Rel (T i ^ 8) 1 := by
  have h : T i ^ 8 = (T i ^ 2) ^ 4 := by rw [← pow_mul]
  rw [h]
  exact ((Derivable.of (Rel.c14 i)).pow 4).trans (Derivable.of (Rel.c5 i))

/-- Every generator has a left inverse modulo the relations. -/
theorem grouplike : Grouplike Rel := by
  intro x
  cases x with
  | ω => exact ⟨W.ω ^ 7, (pow_succ W.ω 7).symm ▸ Derivable.of Rel.c3⟩
  | H₀ => exact ⟨H 0, (sq (H 0)) ▸ Derivable.of (Rel.c4 0)⟩
  | H₁ => exact ⟨H 1, (sq (H 1)) ▸ Derivable.of (Rel.c4 1)⟩
  | S₀ => exact ⟨S 0 ^ 3, (pow_succ (S 0) 3).symm ▸ Derivable.of (Rel.c5 0)⟩
  | S₁ => exact ⟨S 1 ^ 3, (pow_succ (S 1) 3).symm ▸ Derivable.of (Rel.c5 1)⟩
  | T₀ => exact ⟨T 0 ^ 7, (pow_succ (T 0) 7).symm ▸ T_pow_eight 0⟩
  | T₁ => exact ⟨T 1 ^ 7, (pow_succ (T 1) 7).symm ▸ T_pow_eight 1⟩
  | CZ => exact ⟨W.CZ, (sq W.CZ) ▸ Derivable.of Rel.c7⟩

end QCert.CliffordT2
