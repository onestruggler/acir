/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Recovery of all nine subgroup generators

The only hypothesis is preservation of the ambient defining relations by
the two-coset action. Permutation certificates and control removal supply
the full generator recovery required by Reidemeister--Schreier.
-/
import QCert.CliffordCS3.Three.RecoveryGeneration
import QCert.CliffordCS3.Three.PermutationRoutes

namespace QCert.CliffordCS3.Three.GeneratorRecovery

open RecoveryClosure RecoveryGeneration PermutationRoutes

theorem recovered_tokens (hb : HypB) (l : List (Fin 7)) : Recovered (tokens l) := by
  induction l with
  | nil => exact recovered_one
  | cons d l ih => exact recovered_mul (recovered_token hb d) ih

theorem generators_recovered (hb : HypB) : ∀ x : Gen, Recovered (FreeMonoid.of x) := by
  apply recover_generators hb
  · intro j
    fin_cases j
    · exact recovered_congr hb (recovered_tokens hb gray_X0) recover_X0
    · exact recovered_congr hb (recovered_tokens hb gray_X1) recover_X1
    · exact recovered_congr hb (recovered_tokens hb gray_X2) recover_X2
  · exact recovered_congr hb (recovered_tokens hb gray_S01) recover_S01
  · exact recovered_congr hb (recovered_tokens hb gray_S12) recover_S12

theorem hyp_a (hb : HypB) (x : Gen) :
    (hstar act false (fG x)).2 = false ∧
      Derivable Rel (hstar act false (fG x)).1 (FreeMonoid.of x) := by
  simpa only [Recovered, fw, FreeMonoid.lift_eval_of] using generators_recovered hb x

end QCert.CliffordCS3.Three.GeneratorRecovery
