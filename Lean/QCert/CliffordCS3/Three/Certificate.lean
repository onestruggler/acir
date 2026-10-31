/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The complete two-coset certificate

All 49 macro axioms are checked in both cosets. Each table entry carries
its derivation from Figure 2, and the Boolean check verifies the exact
residual words and the resulting cosets.
-/
import QCert.CliffordCS3.Three.Cert.Permutations
import QCert.CliffordCS3.Three.Cert.PhaseCases
import QCert.CliffordCS3.Three.Cert.KCases
import QCert.CliffordCS3.Three.Cert.LocalBlock
import QCert.CliffordCS3.Three.Cert.PointCommutation
import QCert.CliffordCS3.Three.Cert.DisjointK
import QCert.CliffordCS3.Three.Cert.Interchange

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace QCert.CliffordCS3.Three.Certificate

noncomputable section

def table (c : Bool) : List (Rule Rel) :=
  Cert.Permutations.table c ++ Cert.PhaseCases.table c ++ Cert.KCases.table c ++
  Cert.LocalBlock.table c ++ Cert.PointCommutation.table c ++
  Cert.DisjointK.table c ++ Cert.Interchange.table c

theorem complete_check : b2OK h table = true := by decide +kernel

theorem hyp_b (c : Bool) (w v : Word (BianSelingerUn.Gen 8))
    (hwv : BianSelingerUn.Rel 8 w v) :
    (hstar (encodedAction h) c w).2 = (hstar (encodedAction h) c v).2 ∧
      Derivable Rel (hstar (encodedAction h) c w).1 (hstar (encodedAction h) c v).1 :=
  hyp_b_of_check h table complete_check c w v hwv

end
end QCert.CliffordCS3.Three.Certificate
