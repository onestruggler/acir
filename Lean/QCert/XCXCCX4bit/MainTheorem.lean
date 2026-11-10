/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Block normal forms and certified equations for four-bit reversible circuits: the main theorem

Translation of `MainTheorem.agda`.  The theory `T` of Figure 1 (rules
(1)–(7), `SRel`) with the symmetric monoidal laws is sound and complete for
circuits over `X`, `CX` and `CCX` on four wires, and on one, two and three
(Theorem 1.1, Propositions B.1–B.3); the four-wire circuits present
`Alt(16)`, and those on one, two and three wires `Sym(2)`, `Sym(4)`,
`Sym(8)` (Corollary 5.2); every four-wire circuit rewrites to a unique block
normal form `NF(E, B, S)`, the normal forms are in bijection with `Alt(16)`
(Proposition 3.3), and a gate followed by a normal form rewrites to the
normal form with the updated coordinates (Theorem 5.1).  Each statement is
proved by the module that proves it.

The circuits are `Circ n` (the Agda's `Circuit n`), the rules at width `n`
with the structural and swap rules are `VRel SRel n` (the Agda's
`n VRel,_===_`, which its `MainTheorem` renames `n CRel,_===_`; `CRel` is the
framework's type of rule families here), a circuit's function on the states
of its wires is `sem` (the Agda's `⟦_⟧`), compared pointwise by `≐`, and
derivability is `n ⊢ w ≈ v` (the Agda's `⊢ w ≈ v`, its width implicit there).

**The form of the presentations.**  Circuit words are in diagram order
(`w * v` is `w` then `v`), and so is the product of the Agda's groups
`Permutation′-group N` and `Alt-group N` (`∘ₚ`): a circuit's permutation of
the numbered states satisfies `perm (u * v) = perm u ∘ₚ perm v`.  The
framework's `IsPresentationOf Γ sem` reads a word by the monoid homomorphism
`FreeMonoid.lift sem`, and Mathlib's `Equiv.Perm` and `alternatingGroup`
multiply in operator order (`(σ * τ) x = σ (τ x)`).  So the Agda's groups
are, exactly, the opposites `(Equiv.Perm (Fin N))ᵐᵒᵖ` and `(Alt 16)ᵐᵒᵖ`,
and the presentations are stated there, a generator read as `op` of its
permutation (`perm₁ … perm₄`): then a circuit is read as `op` of its own
function on the numbered states, which `lift_perm₁ … lift_perm₄` state.
(The alternative, reading a circuit as the inverse of its permutation in
Mathlib's group, would present the same group but read every circuit
backwards.)  `Gᵐᵒᵖ ≃* G` by inversion (`MulEquiv.inv'`), so the quotient
monoids are isomorphic to Mathlib's groups themselves: `group₁ … group₄`.

The numberings of the states are `Groups.One.enc`, `Width2.enc`,
`Width3.enc` (the reflected Gray code) and `Four.enc` (the lower half in
Gray order, then the upper half reflected); `Four.enc` is the Agda's
re-exported `enc`.

**Additions to the Agda's statements.**  `perm₁ … perm₄` and
`lift_perm₁ … lift_perm₄` (the Agda's `IsPresentationOf` record holds its
semantics as a field; the framework's takes it as an argument), and
`group₁ … group₄`.  `onto` returns a subtype (the Agda's `Σ`).
-/
import QCert.XCXCCX4bit.NormalForm
import Mathlib.Algebra.Group.Equiv.Opposite

namespace QCert.XCXCCX4bit.MainTheorem

open QCert QCert.Circuit CircuitProp IndepProp Alternating
open NormalForm (Coords NF coords absorb)

/-! ## Soundness and completeness (Theorem 1.1, Propositions B.1–B.3) -/

theorem sound {n : ℕ} {w v : Circ n} : n ⊢ w ≈ v → sem w ≐ sem v := fun d =>
  XCXCCX4bit.sound d

theorem complete {w v : Circ 4} : sem w ≐ sem v → 4 ⊢ w ≈ v := fun e =>
  Completeness.complete₄ e

theorem complete₁ {w v : Circ 1} : sem w ≐ sem v → 1 ⊢ w ≈ v := fun e =>
  Width1.complete₁ e

theorem complete₂ {w v : Circ 2} : sem w ≐ sem v → 2 ⊢ w ≈ v := fun e =>
  Width2.complete₂ e

theorem complete₃ {w v : Circ 3} : sem w ≐ sem v → 3 ⊢ w ≈ v := fun e =>
  Width3.complete₃ e

/-! ## The groups of circuits (Corollary 5.2, Propositions B.1–B.3) -/

/-- A one-wire generator's permutation of the two states, in the opposite of
Mathlib's `Sym(2)` (the Agda's diagram-order `Permutation′-group 2`). -/
abbrev perm₁ : Gn 1 → (Equiv.Perm (Fin 2))ᵐᵒᵖ := Groups.perm₁

/-- A two-wire generator's permutation of the four states. -/
abbrev perm₂ : Gn 2 → (Equiv.Perm (Fin 4))ᵐᵒᵖ := Groups.perm₂

/-- A three-wire generator's permutation of the eight states. -/
abbrev perm₃ : Gn 3 → (Equiv.Perm (Fin 8))ᵐᵒᵖ := Groups.perm₃

/-- A four-wire generator's even permutation of the sixteen states, in the
opposite of Mathlib's `Alt(16)` (the Agda's diagram-order `Alt-group 16`). -/
abbrev perm₄ : Gn 4 → (Alt 16)ᵐᵒᵖ := Groups.perm₄

/-- A circuit is read as its function on the numbered states. -/
theorem lift_perm₁ (w : Circ 1) (i : Fin 2) :
    (FreeMonoid.lift perm₁ w).unop i = Groups.One.dec (sem w (Groups.One.enc i)) :=
  Groups.lift_perm₁ w i

theorem lift_perm₂ (w : Circ 2) (i : Fin 4) :
    (FreeMonoid.lift perm₂ w).unop i = Width2.dec (sem w (Width2.enc i)) :=
  Groups.lift_perm₂ w i

theorem lift_perm₃ (w : Circ 3) (i : Fin 8) :
    (FreeMonoid.lift perm₃ w).unop i = Width3.dec (sem w (Width3.enc i)) :=
  Groups.lift_perm₃ w i

theorem lift_perm₄ (w : Circ 4) (i : Fin 16) :
    Alt.perm (FreeMonoid.lift perm₄ w).unop i = Four.dec (sem w (Four.enc i)) :=
  Groups.lift_perm₄ w i

theorem presentation₁ : IsPresentationOf (VRel SRel 1) perm₁ := Groups.presentation₁

theorem presentation₂ : IsPresentationOf (VRel SRel 2) perm₂ := Groups.presentation₂

theorem presentation₃ : IsPresentationOf (VRel SRel 3) perm₃ := Groups.presentation₃

theorem presentation₄ : IsPresentationOf (VRel SRel 4) perm₄ := Groups.presentation₄

/-- `G₁ ≅ Sym(2)`: the one-wire circuits modulo the rules. -/
noncomputable def group₁ : (conGen (VRel SRel 1)).Quotient ≃* Equiv.Perm (Fin 2) :=
  presentation₁.quotientEquiv.trans (MulEquiv.inv' _).symm

/-- `G₂ ≅ Sym(4)`. -/
noncomputable def group₂ : (conGen (VRel SRel 2)).Quotient ≃* Equiv.Perm (Fin 4) :=
  presentation₂.quotientEquiv.trans (MulEquiv.inv' _).symm

/-- `G₃ ≅ Sym(8)`. -/
noncomputable def group₃ : (conGen (VRel SRel 3)).Quotient ≃* Equiv.Perm (Fin 8) :=
  presentation₃.quotientEquiv.trans (MulEquiv.inv' _).symm

/-- `G₄ ≅ Alt(16)`. -/
noncomputable def group₄ : (conGen (VRel SRel 4)).Quotient ≃* Alt 16 :=
  presentation₄.quotientEquiv.trans (MulEquiv.inv' _).symm

/-! ## The block normal form (Theorem 1.1, Proposition 3.3, Theorem 5.1) -/

/-- Every circuit rewrites to the normal form of its coordinates ... -/
theorem normal_form (u : Circ 4) : 4 ⊢ u ≈ NF (coords u) := NormalForm.normal_form u

/-- ... which are determined by its function. -/
theorem unique (c c' : Coords) (e : sem (NF c) ≐ sem (NF c')) :
    (∀ i, c.S i = c'.S i) ∧ (∀ p, c.B p = c'.B p) ∧
      (∀ p, Alt.perm c.E p = Alt.perm c'.E p) :=
  NormalForm.NF_unique c c' e

/-- Every even permutation of the sixteen states is a normal form's. -/
def onto (a : Alt 16) :
    {c : Coords // ∀ i, sem (NF c) (Four.enc i) = Four.enc (Alt.perm a i)} :=
  NormalForm.NF_onto a

/-- A circuit `w` (a gate, say) followed by a normal form rewrites to the
normal form with the updated coordinates (`NormalForm.Absorb` gives them:
`S′ = w⁻¹ S`, `B′ = B A₀`, `E′ B′ = E B A₁`). -/
theorem absorption (c : Coords) (w : Circ 4) : 4 ⊢ w * NF c ≈ NF (absorb c w) :=
  NormalForm.absorption c w

end QCert.XCXCCX4bit.MainTheorem
