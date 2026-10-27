/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three-qubit Clifford+CS: completeness

Words with the same value in `U(8)` are derivably equal under the
relations of Figure 2 (Theorem 3.1 of Bian–Selinger, from their
Theorem 2.1, the presentation of `Uₙ(ℤ[1/2, i])`, by the
Reidemeister–Schreier method).
-/
import QCert.CliffordCS3.Soundness

namespace QCert.CliffordCS3

/-- Completeness of the relations of Figure 2 for `U(8)`. -/
theorem complete : ∀ ⦃w v : Word Gen⦄,
    FreeMonoid.lift sem w = FreeMonoid.lift sem v → Derivable Rel w v := by
  sorry

end QCert.CliffordCS3
