/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Two-qubit Clifford+T: completeness

Words with the same value in `U(4)` are derivably equal under the
relations of Figure 1 (Theorem 5.2 of Bian–Selinger, together with
Greylyn's Theorem 4.1).
-/
import QCert.CliffordT2.Soundness

namespace QCert.CliffordT2

/-- Completeness of the relations of Figure 1 for `U(4)`. -/
theorem complete : ∀ ⦃w v : Word Gen⦄,
    FreeMonoid.lift sem w = FreeMonoid.lift sem v → Derivable Rel w v := by
  sorry

end QCert.CliffordT2
