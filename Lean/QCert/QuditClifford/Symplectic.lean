/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The symplectic action of circuits

A Pauli operator `⊗ᵢ X^{aᵢ} Z^{bᵢ}` is, up to phase, the vector
`v : Fin n → ZMod p × ZMod p` with `v i = (aᵢ, bᵢ)`, wire `0` the bottom
wire.  Conjugation by a Clifford circuit acts on these vectors linearly
and symplectically: by `(a, b) ↦ (-b, a)` for `H` (`H X H† = Z`,
`H Z H† = X⁻¹`), `(a, b) ↦ (a, a + b)` for `S` (`S X S† = X Z`), and for
`CZ` on wires `0, 1` by adding `a₁` to `b₀` and `a₀` to `b₁`.  The scalar
acts trivially.  These conventions were checked against the matrices of
Definition 2.11 numerically for `p = 3, 5, 7`.

`σC p n w` (`SymplecticDef.lean`) is the action of a circuit `w`.
Circuits with the same matrix have the same action (`sigma_of_sem`,
`Weyl.lean`), so the action factors through circuits modulo the rules
(`σG`).
-/
import QCert.QuditClifford.Group
import QCert.QuditClifford.Weyl

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

variable {p} (g : ZMod p) [OddGen p g]

theorem le_ker_σC (n : ℕ) : Cn p g n ≤ Con.ker (σC p n) :=
  Con.conGen_le fun _ _ h => (Con.ker_rel _).2
    (sigma_of_sem p (OddGen.hp2 g) (theory_sound p (OddGen.hp2 g) g (OddGen.ne_zero p g) h))

variable {g} in
/-- The action of a class of circuits. -/
def σG (n : ℕ) : CG p g n →* Function.End (V p n) := (Cn p g n).lift (σC p n) (le_ker_σC g n)

@[simp] theorem σG_mk {n : ℕ} (w : Circ n) : σG n (mk p g n w) = σC p n w := rfl

end QCert.QuditClifford
