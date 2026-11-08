/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: congruences

Translation of `Congruence.agda`: soundness of a congruence from soundness
of its axioms, for a reading of words into a monoid that is a monoid
homomorphism.  (The framework's `derivable_sound` is the same for readings
`FreeMonoid.lift sem`; the semantics here are compositions of homomorphisms.)
-/
import QCert.Presentation

namespace QCert.ToffoliHadamardRS

theorem derivable_hom {X M : Type*} [Monoid M] {Γ : WRel X} (f : Word X →* M)
    (hf : ∀ ⦃w v : Word X⦄, Γ w v → f w = f v) {w v : Word X} (d : Derivable Γ w v) :
    f w = f v := by
  have : conGen Γ ≤ Con.ker f := Con.conGen_le fun x y hxy => (Con.ker_rel _).2 (hf hxy)
  exact (Con.ker_rel _).1 (this d)

end QCert.ToffoliHadamardRS
