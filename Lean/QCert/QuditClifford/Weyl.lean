/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Circuits with the same matrix act alike on Paulis

With the Weyl operators `W(v) = ⊗ᵢ X^{aᵢ} Z^{bᵢ}` (`weylOp`, `WeylOps.lean`),
every circuit `w` satisfies `sem w · W(v) = c · W(σC w v) · sem w` for a
nonzero scalar `c` (`weylActs_sem`), and Weyl operators of distinct vectors
are not proportional (`weylOp_eq_smul`); so circuits with the same matrix
have the same action (`sigma_of_sem`).  (For `p = 2` the phase gate is the
identity matrix while its action is not: the hypothesis `p ≠ 2` is
needed.)
-/
import QCert.QuditClifford.SymplecticDef
import QCert.QuditClifford.Theory
import QCert.QuditClifford.WeylOps

namespace QCert.QuditClifford

open Matrix

variable (p : ℕ) [hp : Fact p.Prime]

/-- Circuits that implement the same matrix act alike on Paulis. -/
theorem sigma_of_sem (hp2 : p ≠ 2) {n : ℕ} {w v : Circ n} (h : sem p n w = sem p n v) :
    σC p n w = σC p n v := by
  refine funext fun x => ?_
  obtain ⟨c, hc, e⟩ := weylActs_sem p hp2 w x
  obtain ⟨c', -, e'⟩ := weylActs_sem p hp2 v x
  have hU : (sem p n v : Op ℂ p n) * star (sem p n v : Op ℂ p n) = 1 :=
    mem_unitaryGroup_iff.1 (sem p n v).2
  rw [h, e'] at e
  have e2 := congrArg (· * star (sem p n v : Op ℂ p n)) e
  simp only [smul_mul_assoc, mul_assoc, hU, mul_one] at e2
  apply weylOp_eq_smul p (d := c⁻¹ * c')
  rw [mul_smul, e2, smul_smul, inv_mul_cancel₀ hc, one_smul]

end QCert.QuditClifford
