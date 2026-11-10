/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The alternating group 𝔄₁₆ as reversible circuits on four wires over X, CX, CCX and Ex: the main theorem

Translation of `MainTheorem.agda`.  The circuits on four wires over NOT,
CNOT, Toffoli and the swap, modulo the seven rules of `Theory` (r1, …, r7,
the rules of Figure 1 of *Block Normal Forms and Certified Equations for
Four-Bit Reversible Circuits*), are a presentation of the even permutations
of the sixteen states.  It is obtained from Lafont's presentation of 𝔄₁₆ by
the cycles `ω₀, …, ω₁₃` (`Lib/Alternating`) in two Reidemeister–Schreier
steps, each a pair of translations that carry the relations of their source
to consequences of those of their target and are inverse on generators.

* From Lafont's words to circuits: `f` reads a gate as a word in the cycles,
  `g` a cycle as a circuit, and the circuits' relation is the translated one
  (`CRel`, `Syntactics`): Lafont's relations read on the cycles' circuits,
  and one rule per gate naming its word.

* From the translated relation to the rules (`RRel`): the same gates and the
  identity translations, so the step is that each relation set's rules
  follow from the other's.  The translated relations are derived from r1, …,
  r7 without another development's theorems: the rules are complete on one,
  two and three wires by a step of the same kind from Symmetric's
  presentation (`presentation₁`, …, `complete₃`), and the four-wire
  derivations rest on those and on rule (7).

Both relation sets are sound and complete for the functions on states, and
every circuit is equal to a unique canonical circuit, the translation of
Lafont's canonical form.

This module collects the statements behind one import: the circuits and
their relations, derivability `⊢ w ≈ v` and `⊢ᴿ w ≈ v`, a circuit's function
`sem` with pointwise equality `≐` and its even permutation `semA`, the
numbering `enc`, `dec` of the states, and the theorems.

**The form of the statements.**  The Agda's `IsGroupIsomorphism … (f ʷ)`
between two word groups is a `MulEquiv` between the monoids of words modulo
the two relations (`(conGen Γ).Quotient`), with the equation saying that it
is `f ʷ` (or the identity) on classes.  The Agda's groups of permutations
multiply in diagram order, as the circuits do, and Mathlib's in operator
order, so the presentations are stated in the opposite groups
`(Equiv.Perm (Fin N))ᵐᵒᵖ` and `(Alt 16)ᵐᵒᵖ`, a generator read as `op` of its
permutation of the numbered states (`perm₁`, `perm₂`, `perm₃`, `permA`), and
then a circuit as `op` of its own (`lift_permA`, with `semA_sem`).

**Additions to the Agda's statements.**  `permA`, `lift_permA`, the three
`_mk` equations, and `group₄ : … ≃* Alt 16`, the quotient isomorphism of the
presentation composed with `Gᵐᵒᵖ ≃* G`.  `canon_onto` returns a subtype (the
Agda's `Σ`).  The Agda's `⟦_⟧`, `⟦_⟧ᴬ` are `sem`, `semA`; its `⋯ᴿ` names
(`presentationᴿ`, …) are `⋯R`.
-/
import QCert.Alt16RevCir.Equivalence
import Mathlib.Algebra.Group.Equiv.Opposite

namespace QCert.Alt16RevCir.MainTheorem

open QCert QCert.Circuit CircuitProp
open Alternating (Alt)

/-- The translated relation on the circuits, with the laws of the swap and
the structural rules (the Agda's `_CRel,_===_`). -/
abbrev CRel (n : ℕ) : WRel (Gn n) := VRel SRel n

/-- Lafont's relation between the words in the cycles `ω₀, …, ω₁₃` (the
Agda's `_LRel_`). -/
abbrev LRel : WRel (Alternating.Gn 16) := Lift Alternating.SRel 16

/-- The rules r1, …, r7, with the laws of the swap and the structural rules
(the Agda's `_RRel,_===_`). -/
abbrev RRel (n : ℕ) : WRel (Gn n) := VRel TRel n

/-- Equality by the translated relation, of four-wire circuits. -/
scoped notation:50 "⊢ " w:51 " ≈ " v:51 => Derivable (CRel 4) w v

/-- Equality by Lafont's relations, of words in the cycles. -/
scoped notation:50 "⊢ᴸ " w:51 " ≈ " v:51 => Derivable LRel w v

/-- Equality by the rules. -/
scoped notation:50 "⊢ᴿ " w:51 " ≈ " v:51 => Derivable (RRel _) w v

/-! ## The first step: Lafont's words and the circuits -/

/-- Each translation carries the relations of its source to consequences of
the relations of its target, -/
theorem f_well_defined {w v : Circ 4} : CRel 4 w v →
    ⊢ᴸ FreeMonoid.lift f w ≈ FreeMonoid.lift f v :=
  Iso.f_well_defined

theorem g_well_defined {u t : Alternating.Circ 16} : LRel u t →
    ⊢ FreeMonoid.lift g u ≈ FreeMonoid.lift g t :=
  Iso.g_well_defined

/-- and the two are inverse to each other on generators. -/
theorem f_left_inv_gen (y : Alternating.Gn 16) :
    ⊢ᴸ FreeMonoid.of y ≈ FreeMonoid.lift f (g y) :=
  Iso.f_left_inv_gen y

theorem g_left_inv_gen (x : Gn 4) : ⊢ FreeMonoid.of x ≈ FreeMonoid.lift g (f x) :=
  Iso.g_left_inv_gen x

/-- So the circuits modulo their rules and the words in the cycles modulo
Lafont's relations are isomorphic groups. -/
theorem grouplike : Grouplike (CRel 4) := Iso.grouplike

theorem grouplikeL : Grouplike LRel := Alternating.grouplike 16

def circuits_iso_cycles : (conGen (CRel 4)).Quotient ≃* (conGen LRel).Quotient :=
  Iso.Theorem_Circuits_iso_Cycles

theorem circuits_iso_cycles_mk (w : Circ 4) :
    circuits_iso_cycles ((conGen (CRel 4)).mk' w) = (conGen LRel).mk' (FreeMonoid.lift f w) :=
  rfl

/-- A generator's even permutation of the sixteen positions, that of its
word in the cycles, in the opposite of Mathlib's `Alt(16)` (the Agda's
diagram-order `Alt-group 16`). -/
abbrev permA : Gn 4 → (Alt 16)ᵐᵒᵖ := Alt16RevCir.permA

/-- A circuit is read as `op` of its even permutation `semA`, that of its
word in the cycles (the Agda's `⟦_⟧ᴬ`). -/
theorem lift_permA (w : Circ 4) : FreeMonoid.lift permA w = MulOpposite.op (semA w) :=
  Alt16RevCir.lift_permA w

/-- With Lafont's theorem, the circuits modulo the translated relation
present 𝔄₁₆. -/
theorem presentation : IsPresentationOf (CRel 4) permA := Alt16RevCir.presentation

/-! ## The second step: the translated relation and the rules -/

/-- Each relation set's rules are consequences of the other's, -/
theorem relations_to_rules {w v : Circ 4} : CRel 4 w v → ⊢ᴿ w ≈ v :=
  Equivalence.s_to_t_ax

theorem rules_to_relations {w v : Circ 4} : RRel 4 w v → ⊢ w ≈ v :=
  Equivalence.t_to_s_ax

/-- so the identity is an isomorphism of the two word groups, -/
theorem grouplikeR : Grouplike (RRel 4) := Equivalence.grouplikeT

def rules_iso_relations : (conGen (RRel 4)).Quotient ≃* (conGen (CRel 4)).Quotient :=
  Equivalence.rules_iso_relations

theorem rules_iso_relations_mk (w : Circ 4) :
    rules_iso_relations ((conGen (RRel 4)).mk' w) = (conGen (CRel 4)).mk' w :=
  rfl

/-- and the first step holds for the rules, with the same translations. -/
def rules_iso_cycles : (conGen (RRel 4)).Quotient ≃* (conGen LRel).Quotient :=
  Equivalence.Theorem_Rules_iso_Cycles

theorem rules_iso_cycles_mk (w : Circ 4) :
    rules_iso_cycles ((conGen (RRel 4)).mk' w) = (conGen LRel).mk' (FreeMonoid.lift f w) :=
  rfl

/-! ## The presentation of 𝔄₁₆ by the rules -/

theorem presentationR : IsPresentationOf (RRel 4) permA := Equivalence.presentationT

/-- The four-wire circuits modulo the rules are Mathlib's `Alt(16)`. -/
noncomputable def group₄ : (conGen (RRel 4)).Quotient ≃* Alt 16 :=
  presentationR.quotientEquiv.trans (MulEquiv.inv' _).symm

/-- Circuits equal by the rules are the same function on states, on any
number of wires, and on four wires the converse holds, -/
theorem soundR {n : ℕ} {w v : Circ n} : ⊢ᴿ w ≈ v → sem w ≐ sem v := fun d =>
  T_sound d

theorem completeR {w v : Circ 4} : sem w ≐ sem v → ⊢ᴿ w ≈ v :=
  Equivalence.completeT

/-- every circuit is equal by the rules to its canonical circuit, and
circuits equal by the rules have the same normal form. -/
theorem normal_formR (w : Circ 4) : ⊢ᴿ canon (nf w) ≈ w :=
  Equivalence.normal_formT w

theorem nf_congR {w v : Circ 4} : ⊢ᴿ w ≈ v → nf w = nf v :=
  Equivalence.nf_congT

/-! ## One, two and three wires -/

/-- A generator's permutation of the two states of one wire, in the opposite
of Mathlib's `Sym(2)`. -/
abbrev perm₁ : Gn 1 → (Equiv.Perm (Fin 2))ᵐᵒᵖ := Width1.step₁.semP

/-- A generator's permutation of the four states of two wires. -/
abbrev perm₂ : Gn 2 → (Equiv.Perm (Fin 4))ᵐᵒᵖ := Width2.step₂.semP

/-- A generator's permutation of the eight states of three wires. -/
abbrev perm₃ : Gn 3 → (Equiv.Perm (Fin 8))ᵐᵒᵖ := Width3.step₃.semP

theorem presentation₁ : IsPresentationOf (RRel 1) perm₁ := ThreeWire.presentation₁

theorem presentation₂ : IsPresentationOf (RRel 2) perm₂ := ThreeWire.presentation₂

theorem presentation₃ : IsPresentationOf (RRel 3) perm₃ := ThreeWire.presentation₃

theorem complete₁ {w v : Circ 1} : sem w ≐ sem v → ⊢ᴿ w ≈ v := ThreeWire.complete₁

theorem complete₂ {w v : Circ 2} : sem w ≐ sem v → ⊢ᴿ w ≈ v := ThreeWire.complete₂

theorem complete₃ {w v : Circ 3} : sem w ≐ sem v → ⊢ᴿ w ≈ v := ThreeWire.complete₃

/-! ## The translated relation and the functions on states -/

/-- A circuit's permutation carries the position of a state to the position
of the state the circuit sends it to. -/
theorem semA_sem (w : Circ 4) (i : Fin 16) : Alt.perm (semA w) i = dec (sem w (enc i)) :=
  Alt16RevCir.semA_sem w i

/-- Two circuits are equal by the rules exactly when they are the same
function. -/
theorem sound {w v : Circ 4} : ⊢ w ≈ v → sem w ≐ sem v := fun d =>
  Alt16RevCir.sound d

theorem complete {w v : Circ 4} : sem w ≐ sem v → ⊢ w ≈ v :=
  Alt16RevCir.complete

/-! ## The normal form -/

/-- A canonical circuit is the translation of Lafont's canonical form. -/
theorem canon_g (x : NF) : canon x = FreeMonoid.lift g (Alternating.inv_nf x) :=
  Alt16RevCir.canon_g x

/-- Every circuit is equal by the rules to its canonical circuit, -/
theorem normal_form (w : Circ 4) : ⊢ canon (nf w) ≈ w :=
  Alt16RevCir.normal_form w

/-- which is its own normal form. -/
theorem nf_canon (x : NF) : nf (canon x) = x :=
  Alt16RevCir.nf_canon x

/-- Canonical circuits with the same function are the same, -/
theorem canon_unique {x y : NF} : sem (canon x) ≐ sem (canon y) → x = y :=
  Alt16RevCir.canon_unique

/-- and every even permutation is carried out by one. -/
def canon_onto (a : Alt 16) : {x : NF // ∀ i, Alt.perm (semA (canon x)) i = Alt.perm a i} :=
  Alt16RevCir.canon_onto a

end QCert.Alt16RevCir.MainTheorem
