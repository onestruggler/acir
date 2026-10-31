/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Certified commutations of the phase and the first six tokens
-/
import QCert.CliffordCS3.Three.PhaseCases

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.Cert.PhaseCases

open QuotientGroup LocalKZ
noncomputable section

def rule (c : Bool) (d : Fin 6) : Rule Rel :=
  if c then
    Rule.ofDerivable (ccZ * token d.castSucc) (token d.castSucc * ccZ)
      (to_derivable (by simpa only [map_mul] using
        Three.PhaseCases.sign_token d))
  else
    Rule.ofDerivable (token d.castSucc) (token d.castSucc) (Derivable.refl _)

def table (c : Bool) : List (Rule Rel) := List.ofFn (rule c)

def indices : List ℕ := [28, 30, 32, 34, 36, 38]

def covers : Bool :=
  [false, true].all fun c => indices.all fun i =>
    let e := M8.D.ax[i]!
    let a := (hstar h c (FreeMonoid.ofList e.1)).1
    let b := (hstar h c (FreeMonoid.ofList e.2)).1
    (table c).any fun r => r.lhs == a.toList && r.rhs == b.toList

theorem covers_true : covers = true := by decide +kernel

end
end QCert.CliffordCS3.Three.Cert.PhaseCases
