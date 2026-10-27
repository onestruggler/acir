/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CNOT-dihedral circuits: soundness

Every relation of Figure 1 and every law of the symmetry holds for the
matrices of Definition 3.1 (Proposition 3.6).  Each is decided exactly on
the phase-affine pairs of its two sides (`pa`), on the wires it is drawn
on; the structural rules are sound for every gate set.
-/
import QCert.CNOTDihedral.PhaseAffine

namespace QCert.CNOTDihedral

/-- Each relation holds for the phase-affine pairs, on its own wires. -/
theorem rel_pa : ∀ k w v, Rel k w v → pa k w = pa k v := by
  intro k w v h
  apply PA.eq_of_check
  cases h with
  | R1 => decide +kernel
  | R2 => decide +kernel
  | R3 => decide +kernel
  | R4 => decide +kernel
  | R5 => decide +kernel
  | R6 => decide +kernel
  | R7 => decide +kernel
  | R8 => decide +kernel
  | R9 => decide +kernel
  | R10 => decide +kernel
  | R11 => decide +kernel
  | R12 => decide +kernel
  | R13 => decide +kernel
  | swap_swap => decide +kernel
  | swap_nat1 g => cases g <;> decide +kernel
  | swap_nat2 g => cases g <;> decide +kernel

/-- Proposition 3.6: the relations are sound. -/
theorem rel_sound : ∀ k w v, Rel k w v → S.sem k w = S.sem k v :=
  fun k w v h => sem_eq_of_pa (rel_pa k w v h)

/-- Every rule of the theory, structural or not, is sound. -/
theorem theory_sound : ∀ n w v, Theory n w v → S.sem n w = S.sem n v :=
  S.lift_sound (S.padded_sound rel_sound)

end QCert.CNOTDihedral
