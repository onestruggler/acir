/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Symplectic completeness

Theorem 4.4 in the form used here: a circuit that acts trivially on Pauli
operators (up to phase) is, modulo the rules, a product of conjugates of
Paulis.  Equivalently, modulo the rules and `X = Z = -ω = 1`, the
symplectic action is faithful.
-/
import QCert.QuditClifford.Pauli

namespace QCert.QuditClifford

variable {p : ℕ} [hp : Fact p.Prime] {g : ZMod p} [OddGen p g]

/-- Theorem 4.4: circuits are complete up to Pauli corrections. -/
theorem symplectic_complete {n : ℕ} {x : CG p g n} (h : σG n x = 1) : x ∈ PauliN p g n := by
  sorry

end QCert.QuditClifford
