/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Discharged elementary cases of the two-coset certificate
-/
import QCert.CliffordCS3.Three.Monomial
import QCert.CliffordCS3.Three.Recovery
import QCert.CliffordCS3.Three.Cert.KOrder

namespace QCert.CliffordCS3.Three

/-- Seven actual involution proofs, used by both coset branches. -/
theorem token_involution (d : Fin 7) :
    Derivable Rel (Cert.token d * Cert.token d) 1 :=
  token_square Monomial.ccZ_square d

/-- The subgroup phase generator is recovered unconditionally. -/
theorem phase_recovered :
    Derivable Rel (hstar h false (Macro.encW M8.D (fG .CS₁₂))).1
      (FreeMonoid.of .CS₁₂) :=
  recover_CS12 (token_involution 6) Monomial.phase_token6_commute Monomial.ccZ_square

/-- The sign atom has order two in the presented group. -/
def signRule : Rule Rel :=
  Rule.ofDerivable (Cert.ccZ * Cert.ccZ) 1 Monomial.ccZ_square

def tokenRules : List (Rule Rel) :=
  List.ofFn fun d : Fin 7 =>
    Rule.ofDerivable (Cert.token d * Cert.token d) 1 (token_involution d)

def phaseRecoveryRule : Rule Rel :=
  Rule.ofDerivable (hstar h false (Macro.encW M8.D (fG .CS₁₂))).1
    (FreeMonoid.of .CS₁₂) phase_recovered

end QCert.CliffordCS3.Three

