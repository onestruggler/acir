/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Soundness of CNOTdihe₂

Every rule of Figure 7 and every law of the symmetry holds in the semantics
of Section 3.1, each decided over ℤ[ω] on row tries.
-/
import QCert.Minimality.CNOTDihedral.Semantics

namespace QCert.Minimality.CNOTDihedral

open Circuit

private theorem go {n : ℕ} {w v : Circuit Gate n}
    (h : (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (scaled.ex v - scaled.ex w)) (evalRows ops n w) =
      (rowsRep 2 n).ops.smul (ZOmega.sqrt2 ^ (scaled.ex w - scaled.ex v)) (evalRows ops n v)) :
    sem.sem n w = sem.sem n v :=
  Qubit.sem_eq_of_rows sem scaled sem_toOps h

/-- Every rule of Figure 7 is sound. -/
theorem sound_ax : ∀ a : Ax, sem.sem a.arity a.sides.1 = sem.sem a.arity a.sides.2
  | .ω8 => go (by decide +kernel)
  | .X2 => go (by decide +kernel)
  | .T8 => go (by decide +kernel)
  | .TX => go (by decide +kernel)
  | .XC => go (by decide +kernel)
  | .B => go (by decide +kernel)
  | .ZC => go (by decide +kernel)
  | .CPh => go (by decide +kernel)
  | .I => go (by decide +kernel)
  | .C2T => go (by decide +kernel)
  | .C3T => go (by decide +kernel)

/-- The laws of the symmetry hold for the swap matrix. -/
theorem sound_sym {k : ℕ} {w v : Circuit Gate k} : Sym Gate.swap k w v → sem.sem k w = sem.sem k v
  | .invol => go (by decide +kernel)
  | .nat1 .X => go (by decide +kernel)
  | .nat1 .T => go (by decide +kernel)
  | .nat2 .CX => go (by decide +kernel)
  | .nat2 .swap => go (by decide +kernel)
  | .nat3 g => nomatch g

/-- Soundness: every equation derivable in CNOTdihe₂ holds in the semantics. -/
theorem sound {n : ℕ} {w v : Circuit Gate n} (h : pres.Proves n w v) : sem.sem n w = sem.sem n v := by
  refine derivable_sound (fun w v r => ?_) h
  refine sem.lift_sound (sem.padded_sound ?_) _ w v r
  intro k w v b
  cases b with
  | sym s => exact sound_sym s
  | ax a _ => exact sound_ax a

end QCert.Minimality.CNOTDihedral
