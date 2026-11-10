/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The isomorphism between the circuits on four wires modulo the rules of Syntactics and Lafont's words in the cycles on sixteen points modulo his relations: a Reidemeister–Schreier step

Translation of `Iso.agda`.  The two rule sets are over different alphabets.
The circuits' are the gates `X`, `CX`, `CCX` and `Ex` on four wires, with
the rules of `Syntactics`, the laws of the swap and the structural rules
(`VRel SRel 4`).  Lafont's are the cycles `ω₀, …, ω₁₃`, with the three
relations of his Theorem 4 and the commutations of cycles three or more
points apart (`Lift Alternating.SRel 16`).  `Translation` has the
translations in both directions: `f` reads a gate as a word in the cycles,
`g` a cycle as a circuit.  The content is that the two relation sets are
equivalent along them:

* `f_well_defined`: every rule of the circuits, translated by `f`, follows
  from Lafont's relations;
* `g_well_defined`: every relation of Lafont's, translated by `g`, follows
  from the circuits' rules;
* `f_left_inv_gen`: every cycle is, by Lafont's relations, the word of its
  circuit;
* `g_left_inv_gen`: every gate is, by the circuits' rules, the circuit of
  its word.

Where the two halves are proved:

* The half towards the circuits is syntactic (`Lemmas`).  The rules of
  `Syntactics` are Lafont's relations read through `g` and one rule per gate
  naming its word, so each instance of his relation goes to one rule
  (`lemma_g_rel`), and each gate is the circuit of its word by its rule, or
  by that of the gate on the bottom wires and the naturality of the swap
  (`lemma_g_f`).

* The half towards Lafont's words is semantic.  A word in the cycles
  permutes the sixteen positions as its circuit maps the sixteen states, and
  conversely (`Bridge.f_sem`, `g_sem_gen`); the circuits' rules are sound for
  the functions on states (`Semantics.ax_sound`); and two words in the cycles
  with the same permutation are equal by Lafont's relations: the
  completeness half of his theorem.  So no derivation between the words of
  the gates, some of a hundred cycles, is written out.

`Lib/Morphism` turns the four facts into the isomorphism.

**Deviations from the Agda.**  The Agda's module `Theorem` is the namespace
`Iso`.  The isomorphism is a `MulEquiv` of the quotient monoids, `f ʷ` on
classes (`Morphism.RSStep.iso`, `iso_mk`), where the Agda states that `f ʷ`
is a group isomorphism of the two word groups.
-/
import QCert.Alt16RevCir.Bridge
import QCert.Alt16RevCir.Lemmas
import QCert.Alt16RevCir.Lib.Morphism
import QCert.Alt16RevCir.Lib.Alternating.Presentation

namespace QCert.Alt16RevCir.Iso

open QCert QCert.Circuit CircuitProp

/-! ## The isomorphism -/

/-- `f`: circuits → Lafont's words.  A rule of the circuits equates two
circuits with the same function on states, so their words have the same
permutation of the positions, and are equal by completeness. -/
theorem f_well_defined {w v : Circ 4} (r : VRel SRel 4 w v) :
    Derivable (Lift Alternating.SRel 16) (FreeMonoid.lift f w) (FreeMonoid.lift f v) :=
  Alternating.completeness fun i =>
    (f_sem w i).trans ((congrArg dec (ax_sound r (enc i))).trans (f_sem v i).symm)

/-- `g`: Lafont's words → circuits.  Each instance of his relation is read
as a rule of `Syntactics`. -/
theorem g_well_defined {u t : Alternating.Circ 16} (r : Lift Alternating.SRel 16 u t) :
    4 ⊢ FreeMonoid.lift g u ≈ FreeMonoid.lift g t :=
  lemma_g_rel 0 rfl r

/-- A cycle and the word of its circuit have the same permutation. -/
theorem f_left_inv_gen (y : Alternating.Gn 16) :
    Derivable (Lift Alternating.SRel 16) (FreeMonoid.of y) (FreeMonoid.lift f (g y)) :=
  Alternating.completeness fun i => (g_sem_gen y i).symm.trans (f_sem (g y) i).symm

theorem g_left_inv_gen (x : Gn 4) : 4 ⊢ FreeMonoid.of x ≈ FreeMonoid.lift g (f x) :=
  lemma_g_f x

/-- The four facts. -/
theorem rsStep : Morphism.RSStep (VRel SRel 4) (Lift Alternating.SRel 16) f g where
  f_well_defined := f_well_defined
  f_left_inv_gen := f_left_inv_gen
  g_well_defined := g_well_defined
  g_left_inv_gen := g_left_inv_gen

/-! ### Group-likeness of the circuits' rules

Transported rather than reproved: `g_well_defined` lifts to the whole
congruence, so the inverse of a gate `x` is the circuit of the inverse, in
Lafont's word group, of the word of `x`. -/

theorem grouplike : Grouplike (VRel SRel 4) :=
  rsStep.grouplike (Alternating.grouplike 16)

/-! ### The theorem -/

/-- The circuits modulo the rules of `Syntactics` and the words in the
cycles modulo Lafont's relations are isomorphic, by `f ʷ`. -/
def Theorem_Circuits_iso_Cycles :
    (conGen (VRel SRel 4)).Quotient ≃* (conGen (Lift Alternating.SRel 16)).Quotient :=
  rsStep.iso

end QCert.Alt16RevCir.Iso
