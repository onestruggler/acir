/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of CliffCS₂ up to three qubits (Theorem 22 (5))

Theorem 21 for CliffCS₂ at each width up to three, from sources whose
scalars are the powers of `i`, refined by a central `w` with `w² = i`
(Appendix I; `refine_complete`, Lemma 50, with "no hidden phases" proved):

* with no wire and on one wire from Bian and Selinger's presentation of
  `Uₘ(ℤ[½, i])` in dimensions `1` and `2` (`complete₀_of_source`,
  `complete₁_of_source`), which the paper leaves implicit.

Each takes the completeness of its source as a hypothesis.
-/
import QCert.Minimality.CliffordCS.Derivations
import QCert.BianSelingerUn.Theorem

namespace QCert.Minimality.CliffordCS

open Matrix QCert.Circuit OmegaParity

/-- Theorem 22 (5) on one wire, from the completeness of Bian and Selinger's
presentation in dimension `2`. -/
theorem complete₁_of_source
    (hsrc : ∀ a b : Word (QCert.BianSelingerUn.Gen 2),
      FreeMonoid.lift (QCert.BianSelingerUn.sem 2) a =
        FreeMonoid.lift (QCert.BianSelingerUn.sem 2) b →
        Derivable (QCert.BianSelingerUn.Rel 2) a b)
    (w v : Circuit Gate 1) (h : sem.sem 1 w = sem.sem 1 v) : pres.Proves 1 w v :=
  complete_of_flat (n := 1) scaled sem sem_toOps (Lift Th 1)
    (RRel (QCert.BianSelingerUn.Rel 2) (UN.gi 2))
    ((QOmega.toC.mapMatrix : Matrix (Fin 2) (Fin 2) QOmega →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom.comp
      (FreeMonoid.lift (matR UN.matU)))
    (MonoidHom.id _) Function.injective_id (matR UN.matU)
    (fun y => by rw [MonoidHom.id_apply, MonoidHom.comp_apply, FreeMonoid.lift_eval_of]; rfl)
    W1.e W1.e_ok W1.D
    (fun a b hab => refine_complete (UN.complete_Q hsrc) UN.sound_Q W1.gi_eq UN.matU_even
      (UN.lift_ne_zero (by norm_num)) a b (UN.mapC_injective hab))
    (fun _ _ hab => derivable_map_of _ _ W1.D (fun _ _ r => W1.rel_derivable r) hab)
    (derivable_lift_comp W1.e W1.D W1.DE_gen) w v h

/-- Theorem 22 (5) with no wire, from the completeness of Bian and Selinger's
presentation in dimension `1`. -/
theorem complete₀_of_source
    (hsrc : ∀ a b : Word (QCert.BianSelingerUn.Gen 1),
      FreeMonoid.lift (QCert.BianSelingerUn.sem 1) a =
        FreeMonoid.lift (QCert.BianSelingerUn.sem 1) b →
        Derivable (QCert.BianSelingerUn.Rel 1) a b)
    (w v : Circuit Gate 0) (h : sem.sem 0 w = sem.sem 0 v) : pres.Proves 0 w v :=
  complete_of_flat (n := 0) scaled sem sem_toOps (Lift Th 0)
    (RRel (QCert.BianSelingerUn.Rel 1) (UN.gi 1))
    ((QOmega.toC.mapMatrix : Matrix (Fin 1) (Fin 1) QOmega →+* Matrix (Fin 1) (Fin 1) ℂ).toMonoidHom.comp
      (FreeMonoid.lift (matR UN.matU)))
    (MonoidHom.id _) Function.injective_id (matR UN.matU)
    (fun y => by rw [MonoidHom.id_apply, MonoidHom.comp_apply, FreeMonoid.lift_eval_of]; rfl)
    W0.e W0.e_ok W0.D
    (fun a b hab => refine_complete (UN.complete_Q hsrc) UN.sound_Q W0.gi_eq UN.matU_even
      (UN.lift_ne_zero (by norm_num)) a b (UN.mapC_injective hab))
    (fun _ _ hab => derivable_map_of _ _ W0.D (fun _ _ r => W0.rel_derivable r) hab)
    (derivable_lift_comp W0.e W0.D W0.DE_gen) w v h

end QCert.Minimality.CliffordCS
