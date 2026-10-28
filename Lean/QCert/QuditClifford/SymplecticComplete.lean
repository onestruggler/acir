/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symplectic completeness

Theorem 4.4 in the form used here: a circuit that acts trivially on Pauli
operators (up to phase) is, modulo the rules, a product of conjugates of
Paulis.  Equivalently, modulo the rules and `X = Z = -ω = 1`, the
symplectic action is faithful.

The proof is the stabiliser chain of `Step2.stab_all`, which needs only the
local facts on two and three wires, `lf2` (`Width2.lean`) and `lf3`
(`Width3.lean`), all derived from the rules of Figure 1.
-/
import QCert.QuditClifford.Width3

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-- Circuits modulo the rules and the Paulis act faithfully, at every width. -/
theorem faith_all : ∀ n, Faith p g n
  | 0 => faith_zero
  | m + 1 => (stab_all lf2 lf3 m).2.2

/-- Theorem 4.4: circuits are complete up to Pauli corrections. -/
theorem symplectic_complete {n : ℕ} {x : CG p g n} (h : σG n x = 1) : x ∈ PauliN p g n := by
  have h1 : σh n (QuotientGroup.mk' (PauliN p g n) x) = 1 := h
  have h2 := faith_all (p := p) (g := g) n _ h1
  exact (QuotientGroup.eq_one_iff _).1 h2

end QCert.QuditClifford
