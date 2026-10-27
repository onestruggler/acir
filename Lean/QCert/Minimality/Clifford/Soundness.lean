/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of Cliff₂

Every rule of Figure 2 and every law of the symmetry holds in the semantics
of Section 3.1, each decided over ℤ[ω] on row tries; hence every derivable
equation holds.
-/
import QCert.Minimality.Clifford.Semantics

namespace QCert.Minimality.Clifford

open Circuit

/-- Every rule of Figure 2 is sound. -/
theorem sound_ax : ∀ a : Ax, sem.sem a.arity a.sides.1 = sem.sem a.arity a.sides.2
  | .ω8 => sem_eq_of_rows (by decide +kernel)
  | .H2 => sem_eq_of_rows (by decide +kernel)
  | .S4 => sem_eq_of_rows (by decide +kernel)
  | .E => sem_eq_of_rows (by decide +kernel)
  | .CPh => sem_eq_of_rows (by decide +kernel)
  | .B => sem_eq_of_rows (by decide +kernel)
  | .CZ => sem_eq_of_rows (by decide +kernel)
  | .I => sem_eq_of_rows (by decide +kernel)

/-- The laws of the symmetry hold for the swap matrix. -/
theorem sound_sym {k : ℕ} {w v : Circuit Gate k} : Sym Gate.swap k w v → sem.sem k w = sem.sem k v
  | .invol => sem_eq_of_rows (by decide +kernel)
  | .nat1 .H => sem_eq_of_rows (by decide +kernel)
  | .nat1 .S => sem_eq_of_rows (by decide +kernel)
  | .nat2 .CX => sem_eq_of_rows (by decide +kernel)
  | .nat2 .swap => sem_eq_of_rows (by decide +kernel)
  | .nat3 g => nomatch g

/-- Soundness: every equation derivable in Cliff₂ holds in the semantics. -/
theorem sound {n : ℕ} {w v : Circuit Gate n} (h : pres.Proves n w v) : sem.sem n w = sem.sem n v := by
  refine derivable_sound (fun w v r => ?_) h
  refine sem.lift_sound (sem.padded_sound ?_) _ w v r
  intro k w v b
  cases b with
  | sym s => exact sound_sym s
  | ax a _ => exact sound_ax a

end QCert.Minimality.Clifford
