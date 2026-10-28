/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Circuits with the same matrix act alike on Paulis

With the Weyl operators `W(v) = ⊗ᵢ X^{aᵢ} Z^{bᵢ}`, every circuit `w`
satisfies `sem w · W(v) = c · W(σC w v) · sem w` for a nonzero scalar `c`,
and Weyl operators of distinct vectors are not proportional; so circuits
with the same matrix have the same action (`sigma_of_sem`).  (For `p = 2`
the phase gate is the identity matrix while its action is not: the
hypothesis `p ≠ 2` is needed.)
-/
import QCert.QuditClifford.SymplecticDef
import QCert.QuditClifford.Theory

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

/-- Circuits that implement the same matrix act alike on Paulis. -/
theorem sigma_of_sem (hp2 : p ≠ 2) {n : ℕ} {w v : Circ n} (h : sem p n w = sem p n v) :
    σC p n w = σC p n v := by
  sorry

end QCert.QuditClifford
