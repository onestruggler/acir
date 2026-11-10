/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The circuits on four wires over X, CX, CCX and Ex present 𝔄₁₆

Translation of `Presentation.agda`.  `Iso` makes the translation `f ʷ` of
circuits into words in Lafont's cycles an isomorphism of the two word
groups, and Lafont's Theorem 4 (`Lib/Alternating/Presentation`) makes the
reading of those words as even permutations of sixteen points an
isomorphism onto 𝔄₁₆.  Their composite is the presentation: a circuit is
read as the even permutation of its word, `semA` (the Agda's `⟦_⟧ᴬ`).

That permutation is the circuit's own action: along the Gray-code numbering
of the sixteen states it permutes the positions as the circuit maps the
states (`semA_sem`).  So the rules are sound and complete for the functions
on states, too: two circuits are equal by the rules exactly when they are
the same function (`Semantics.sound`, `complete`).

**Deviations from the Agda.**  The Agda's group `Alt-group 16` multiplies in
diagram order and Mathlib's `alternatingGroup` in operator order, so the
presentation is stated in the opposite group: a generator is read as `op` of
the even permutation of its word (`permA`), and a circuit then as `op` of
its own (`lift_permA`).  The Agda composes two group isomorphisms; here the
reading `semA` is shown compatible with the rules, injective modulo them and
onto, from the same two facts (`Morphism.presentation_of`), once for any
relation on the circuits that is sound and complete for the functions on
states (`presentation_semA`, which `Equivalence` uses again for the rules
(1)–(7)).
-/
import QCert.Alt16RevCir.Iso

namespace QCert.Alt16RevCir

open QCert QCert.Circuit CircuitProp
open Alternating (Alt)

/-! ## A circuit as an even permutation -/

/-- The permutation of the circuit's word in the cycles (the Agda's
`⟦_⟧ᴬ`). -/
def semA (w : Circ 4) : Alt 16 := Alternating.sem (FreeMonoid.lift f w)

/-- It carries the position of a state to the position of the state the
circuit sends it to (the Agda's `⟦⟧ᴬ-sem`). -/
theorem semA_sem (w : Circ 4) (i : Fin 16) : Alt.perm (semA w) i = dec (sem w (enc i)) :=
  f_sem w i

/-- Circuits with the same function have the same permutation. -/
theorem semA_congr {w v : Circ 4} (e : sem w ≐ sem v) : semA w = semA v :=
  Alternating.Alt.ext fun i =>
    (semA_sem w i).trans ((congrArg dec (e (enc i))).trans (semA_sem v i).symm)

/-- Circuits with the same permutation have the same function. -/
theorem feq_of_semA {w v : Circ 4} (e : semA w = semA v) : sem w ≐ sem v := fun x => by
  have h := congrArg (fun p : Alt 16 => enc (Alt.perm p (dec x))) e
  simpa only [semA_sem, enc_dec] using h

/-! ## Soundness and completeness for the functions on states -/

/-- Two circuits with the same function have the same permutation, and the
presentation's reading is injective. -/
theorem complete {w v : Circ 4} (e : sem w ≐ sem v) : 4 ⊢ w ≈ v :=
  Iso.rsStep.injective (Alternating.completeness fun i =>
    (f_sem w i).trans ((congrArg dec (e (enc i))).trans (f_sem v i).symm))

/-! ## The presentation -/

theorem semA_one : semA 1 = 1 := by
  rw [semA, map_one]; exact Alternating.sem_one'

/-- `semA` reverses products in Mathlib's (operator-order) group. -/
theorem semA_mul (a b : Circ 4) : semA (a * b) = semA b * semA a := by
  rw [semA, map_mul]; exact Alternating.sem_mul' _ _

/-- Every even permutation of the positions is a circuit's: the circuit of a
word in the cycles that Lafont's theorem gives. -/
theorem semA_onto (a : Alt 16) : ∃ w : Circ 4, semA w = a := by
  obtain ⟨u, hu⟩ := (Alternating.presentation 16).surjective (MulOpposite.op a)
  rw [Alternating.lift_semOp] at hu
  refine ⟨FreeMonoid.lift g u, Alternating.Alt.ext fun i => ?_⟩
  rw [← MulOpposite.op_injective hu]
  exact (Alternating.soundness (Iso.rsStep.right_inv u) i).symm

/-- The semantics of a generator, in the opposite of Mathlib's alternating
group (the Agda's diagram-order `Alt-group 16`). -/
def permA (x : Gn 4) : (Alt 16)ᵐᵒᵖ := MulOpposite.op (semA (FreeMonoid.of x))

/-- A relation on the four-wire circuits whose congruence is equality of the
permutations presents 𝔄₁₆. -/
theorem presentation_semA {Γ : WRel (Gn 4)} (gl : Grouplike Γ)
    (snd : ∀ {a b : Circ 4}, Derivable Γ a b → semA a = semA b)
    (cmp : ∀ {a b : Circ 4}, semA a = semA b → Derivable Γ a b) :
    IsPresentationOf Γ permA :=
  Morphism.presentation_of gl semA semA_one semA_mul snd cmp semA_onto

/-- The isomorphism of `Iso`, followed by Lafont's. -/
theorem presentation : IsPresentationOf (VRel SRel 4) permA :=
  presentation_semA Iso.grouplike (fun d => semA_congr (sound d))
    (fun e => complete (feq_of_semA e))

/-- A circuit is read as `op` of its even permutation. -/
theorem lift_permA (w : Circ 4) : FreeMonoid.lift permA w = MulOpposite.op (semA w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, semA_one]; rfl
  | mul_of x w ih =>
    rw [map_mul, ih, FreeMonoid.lift_eval_of, permA, ← MulOpposite.op_mul, ← semA_mul]

end QCert.Alt16RevCir
