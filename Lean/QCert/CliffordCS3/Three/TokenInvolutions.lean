/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Involutions among the Gray-path transpositions

These derivations reduce every token square to the square of CCZ. The
remaining hypothesis is supplied by the three-wire phase calculation.
-/
import QCert.CliffordCS3.Rewrite
import QCert.CliffordCS3.Three.Checks

namespace QCert.CliffordCS3.Three

theorem conjugate_square {a b u : Word Gen}
    (hab : Derivable Rel (a * b) 1)
    (hba : Derivable Rel (b * a) 1)
    (hu : Derivable Rel (u * u) 1) :
    Derivable Rel ((a * u * b) * (a * u * b)) 1 := by
  have h1 := (hba.mul_left (a * u)).mul_right (u * b)
  have h2 := (hu.mul_left a).mul_right b
  exact (by simpa only [mul_assoc, mul_one, one_mul] using h1 :
    Derivable Rel ((a * u * b) * (a * u * b)) (a * u * u * b)).trans
    ((by simpa only [mul_assoc, mul_one, one_mul] using h2 :
      Derivable Rel (a * u * u * b) (a * b)).trans hab)

theorem K_inverse (q : Fin 3) :
    Derivable Rel (W.K q * (W.I * W.K q)) 1 := by
  fin_cases q
  · exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Ku * (Two.W2.I * Two.W2.Ku)) (v := 1) (by decide +kernel))
  · exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Kl * (Two.W2.I * Two.W2.Kl)) (v := 1) (by decide +kernel))
  · exact Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.Kl * (Two.W2.I * Two.W2.Kl)) (v := 1) (by decide +kernel))

theorem K_inverse' (q : Fin 3) :
    Derivable Rel ((W.I * W.K q) * W.K q) 1 := by
  fin_cases q
  · exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := (Two.W2.I * Two.W2.Ku) * Two.W2.Ku) (v := 1) (by decide +kernel))
  · exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := (Two.W2.I * Two.W2.Kl) * Two.W2.Kl) (v := 1) (by decide +kernel))
  · exact Two.derivable_embed 1 (Two.derivable_of_check2
      (w := (Two.W2.I * Two.W2.Kl) * Two.W2.Kl) (v := 1) (by decide +kernel))

theorem X_square (q : Fin 3) : Derivable Rel (W.X q * W.X q) 1 := by
  fin_cases q
  · exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Xu * Two.W2.Xu) (v := 1) (by decide +kernel))
  · exact Two.derivable_embed 0 (Two.derivable_of_check2
      (w := Two.W2.Xl * Two.W2.Xl) (v := 1) (by decide +kernel))
  · exact Two.derivable_embed 1 (Two.derivable_of_check2
      (w := Two.W2.Xl * Two.W2.Xl) (v := 1) (by decide +kernel))

def ccx (q : Fin 3) : Word Gen := W.K q * Cert.ccZ * (W.I * W.K q)

theorem ccx_square (q : Fin 3) (hQ : Derivable Rel (Cert.ccZ * Cert.ccZ) 1) :
    Derivable Rel (ccx q * ccx q) 1 :=
  conjugate_square (K_inverse q) (K_inverse' q) hQ

theorem X_conjugate_square (q : Fin 3) {u : Word Gen}
    (hu : Derivable Rel (u * u) 1) :
    Derivable Rel ((W.X q * u * W.X q) * (W.X q * u * W.X q)) 1 :=
  conjugate_square (X_square q) (X_square q) hu

/-- All seven Gray-path tokens are involutions once the phase square is proved. -/
theorem token_square (hQ : Derivable Rel (Cert.ccZ * Cert.ccZ) 1) (d : Fin 7) :
    Derivable Rel (Cert.token d * Cert.token d) 1 := by
  fin_cases d
  · simpa only [mul_assoc] using X_conjugate_square 1 (ccx_square 0 hQ)
  · simpa only [mul_assoc] using X_conjugate_square 0 (X_conjugate_square 1 (ccx_square 2 hQ))
  · simpa only [mul_assoc] using X_conjugate_square 1 (X_conjugate_square 2 (ccx_square 0 hQ))
  · simpa only [mul_assoc] using X_conjugate_square 2 (ccx_square 1 hQ)
  · simpa only [mul_assoc] using X_conjugate_square 2 (ccx_square 0 hQ)
  · simpa only [mul_assoc] using X_conjugate_square 0 (ccx_square 2 hQ)
  · exact ccx_square 0 hQ

end QCert.CliffordCS3.Three

