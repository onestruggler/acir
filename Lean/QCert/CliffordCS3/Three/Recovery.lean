/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Recovery of subgroup generators

The CS₁₂ recovery equation uses only the last Gray-path transposition,
its commutation with CS₁₂, and the square of the one-point sign.
-/
import QCert.CliffordCS3.Three.Checks

namespace QCert.CliffordCS3.Three

open Macro

theorem recover_phase {t p q : Word Gen}
    (ht : Derivable Rel (t * t) 1)
    (hp : Derivable Rel (t * p) (p * t))
    (hq : Derivable Rel (q * q) 1) :
    Derivable Rel (t * p * t * q * q) p := by
  have h₁ := ((hp.mul_right t).mul_right q).mul_right q
  have h₂ := (ht.mul_left p).mul_right (q * q)
  have h₃ := hq.mul_left p
  apply h₁.trans
  apply (by simpa only [mul_assoc, mul_one] using h₂ :
    Derivable Rel (p * t * t * q * q) (p * (q * q))).trans
  simpa only [mul_one] using h₃

/-- The finite computation of the CS₁₂ round trip, before using any relation. -/
theorem residual_CS12 :
    (hstar h false (encW M8.D (fG .CS₁₂))).1 =
      Cert.token 6 * phase * Cert.token 6 * Cert.ccZ * Cert.ccZ := by
  rfl

/-- CS₁₂ is recovered from the three elementary monomial equations. -/
theorem recover_CS12
    (ht : Derivable Rel (Cert.token 6 * Cert.token 6) 1)
    (hp : Derivable Rel (Cert.token 6 * phase) (phase * Cert.token 6))
    (hq : Derivable Rel (Cert.ccZ * Cert.ccZ) 1) :
    Derivable Rel (hstar h false (encW M8.D (fG .CS₁₂))).1 (FreeMonoid.of .CS₁₂) := by
  rw [residual_CS12]
  exact recover_phase ht hp hq

end QCert.CliffordCS3.Three
