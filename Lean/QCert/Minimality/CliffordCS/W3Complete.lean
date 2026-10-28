/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness of CliffCS₂ on three wires

Theorem 22 (5) on three wires: by transfer from Bian and Selinger's
three-qubit Clifford+CS presentation (`QCert.CliffordCS3`), refined by the
new scalar `w` with `w² = i` (Appendix I, `refine_complete`), the source's
relations read reversed as the paper draws them (`complete_of_flat_rev`,
every generator's matrix being symmetric).  The encoding and the decoding
are in `W3Base`, the decoded relations and the round trips in `W3Rels`.
-/
import QCert.Minimality.CliffordCS.W3Rels
import QCert.Minimality.CliffordCS.W3Enc

namespace QCert.Minimality.CliffordCS

open Matrix QCert.Circuit OmegaParity

/-- Theorem 22 (5) on three wires, from the completeness of Bian and
Selinger's three-qubit presentation. -/
theorem complete₃_of_source
    (hsrc : ∀ a b : Word QCert.CliffordCS3.Gen,
      FreeMonoid.lift QCert.CliffordCS3.sem a = FreeMonoid.lift QCert.CliffordCS3.sem b →
        Derivable QCert.CliffordCS3.Rel a b)
    (w v : Circuit Gate 3) (h : sem.sem 3 w = sem.sem 3 v) : pres.Proves 3 w v :=
  complete_of_flat_rev (n := 3) scaled sem sem_toOps (Lift Th 3)
    (RRel QCert.CliffordCS3.Rel W3.gi)
    ((QOmega.toC.mapMatrix : Matrix (Fin 8) (Fin 8) QOmega →+* Matrix (Fin 8) (Fin 8) ℂ).toMonoidHom.comp
      (FreeMonoid.lift (matR W3.matS)))
    (MonoidHom.id _) Function.injective_id (matR W3.matS) W3.matS_symm
    (fun y => by rw [MonoidHom.id_apply, MonoidHom.comp_apply, FreeMonoid.lift_eval_of]; rfl)
    W3.e W3.e_ok W3.D
    (fun a b hab => refine_complete (W3.complete_S hsrc) W3.sound_S W3.gi_eq W3.matS_even
      W3.lift_ne_zero a b (UN.mapC_injective hab))
    (fun _ _ r => W3.rel_derivable r)
    (derivable_lift_comp W3.e W3.D W3.DE_gen) w v h

end QCert.Minimality.CliffordCS
