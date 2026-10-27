/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness for the pairs `(g, q)`

Circuits with the same pair `(g, q)` (affine relabelling and phase
function) are equal in the theory of their fragment: Theorem 1 (level `0`)
and Theorem 2 (levels `1`, `2`, `3`) of Blake (arXiv:2603.06466), in the
form to which `Theorem` reduces the matrix statements.
-/
import QCert.PhaseAffine.Soundness
import QCert.PhaseAffine.Derive

namespace QCert.PhaseAffine

variable {d : ℕ} [Fact d.Prime]

/-- Theorem 1 for the pairs: affine circuits. -/
theorem complete_lin0 (n : ℕ) (w v : C d 0 n)
    (h : (gateData d 0).sem n w = (gateData d 0).sem n v) : Derivable (theory d 0 n) w v := by
  sorry

/-- Theorem 2 for the pairs, `LinPhase_d`. -/
theorem complete_lin1 (n : ℕ) (w v : C d 1 n)
    (h : (gateData d 1).sem n w = (gateData d 1).sem n v) : Derivable (theory d 1 n) w v := by
  sorry

/-- Theorem 2 for the pairs, `QuadPhase_d`, `d` odd. -/
theorem complete_quad (hd : d ≠ 2) (n : ℕ) (w v : C d 2 n)
    (h : (gateData d 2).sem n w = (gateData d 2).sem n v) : Derivable (theory d 2 n) w v := by
  sorry

/-- Theorem 2 for the pairs, `CubicPhase_d`, `d > 3`. -/
theorem complete_cube (hd : 3 < d) (n : ℕ) (w v : C d 3 n)
    (h : (gateData d 3).sem n w = (gateData d 3).sem n v) : Derivable (theory d 3 n) w v := by
  sorry

end QCert.PhaseAffine
