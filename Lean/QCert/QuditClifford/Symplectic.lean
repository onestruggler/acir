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

`σC p n w` is the action of a circuit `w`, a monoid homomorphism into the
endomorphisms of `V p n` (composition in operator order).  Circuits with
the same matrix have the same action (`sigma_of_sem`), so the action
factors through circuits modulo the rules (`σG`).
-/
import QCert.QuditClifford.Group

namespace QCert.QuditClifford

variable (p : ℕ) [hp : Fact p.Prime]

/-- Pauli operators modulo phases on `n` wires: `(x, z)` exponents per wire. -/
abbrev V (n : ℕ) := Fin n → ZMod p × ZMod p

/-- The action of a one-qudit gate on the exponents `(x, z)` of `X^x Z^z`. -/
def act1 : Gate 1 → ZMod p × ZMod p → ZMod p × ZMod p
  | .H => fun u => (-u.2, u.1)
  | .S => fun u => (u.1, u.1 + u.2)

/-- The action of a generator. -/
def σGen : {n : ℕ} → Gen Gate n → V p n → V p n
  | _, .gate0 _ => id
  | _, .gate1 h => fun v => Function.update v 0 (act1 p h (v 0))
  | _, .gate2 .CZ => fun v =>
      Function.update (Function.update v 0 ((v 0).1, (v 0).2 + (v 1).1)) 1
        ((v 1).1, (v 1).2 + (v 0).1)
  | _, .gate3 h => nomatch h
  | _, .up g => fun v => Fin.cons (v 0) (σGen g (Fin.tail v))

/-- The action of a circuit, in operator order. -/
def σC (n : ℕ) : Circ n →* Function.End (V p n) :=
  FreeMonoid.lift fun g => (σGen p g : Function.End (V p n))

theorem σC_of {n : ℕ} (g : Gen Gate n) : σC p n (FreeMonoid.of g) = σGen p g := by
  simp [σC]

/-- Circuits that implement the same matrix act alike on Paulis. -/
theorem sigma_of_sem {n : ℕ} {w v : Circ n} (h : sem p n w = sem p n v) : σC p n w = σC p n v := by
  sorry

variable {p} (g : ZMod p) [OddGen p g]

theorem le_ker_σC (n : ℕ) : Cn p g n ≤ Con.ker (σC p n) :=
  Con.conGen_le fun _ _ h => (Con.ker_rel _).2
    (sigma_of_sem p (theory_sound p (OddGen.hp2 g) g (OddGen.ne_zero p g) h))

variable {g} in
/-- The action of a class of circuits. -/
def σG (n : ℕ) : CG p g n →* Function.End (V p n) := (Cn p g n).lift (σC p n) (le_ker_σC g n)

@[simp] theorem σG_mk {n : ℕ} (w : Circ n) : σG n (mk p g n w) = σC p n w := rfl

end QCert.QuditClifford
