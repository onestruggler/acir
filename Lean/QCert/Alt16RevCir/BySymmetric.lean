/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The Reidemeister–Schreier step from Symmetric's presentation of the permutations of N points to the rules (1)–(7) on k wires

Translation of `BySymmetric.agda`.  Below four wires the circuits over `X`,
`CX`, `CCX` and `Ex` are all the permutations of the states, and
`Lib/Symmetric` presents those by the transpositions of two consecutive
points, with the Coxeter relations.  This module is the step from that
presentation to the rules of `Theory` at a width `k` with `N` states,
generic in `k`: the same step as `Iso`'s from Lafont's presentation, laid
out in the same way.

The translations.  `g` reads the transposition of the points `d`, `d + 1` as
a circuit `Θ d`, and `f` reads a gate as a word in the transpositions.

The two relation sets.  Towards the circuits the step asks for the Coxeter
relations between the `Θ d` (`order`, `braid`, `far`) and for each gate to
be the circuit of its word (`gate`): derivations from the rules, which
`Width2` and `Width3` supply.  Towards the transpositions it is semantic, as
in `Iso`: the rules are sound for functions on states, a word in the
transpositions permutes the positions as its circuit maps the states
(`f_sem_gen`, `g_sem_gen`), and Symmetric's presentation is complete.

The result is that `f ʷ` is an isomorphism of the presented groups, hence
that the rules present the permutations of the `N` states and are complete
for functions on the states of `k` wires.

**Deviations from the Agda.**

* The Agda's module `Step`, parameterised by the translations, the
  numbering and the hypotheses, is the structure `Step k N` with those
  fields, and its contents are the lemmas of the namespace `Step`.
* A letter of `Lib/Symmetric` is the index of its transposition (`SG N`),
  where the Agda's is the generator `σ` under some number of shifts.  So `g`
  is `fun y => Θ y.1`, the Agda's recursion `gᵈ` on the shifts with `gᵈ-↑`
  and `no-gen₁` is not needed, and `lemma_g_rel` has one case for each of
  the relations `order`, `braid`, `far` of `SymRel`.
* The isomorphism is a `MulEquiv` of the quotient monoids (`Lib/Morphism`),
  and the presentation is stated in the opposite of Mathlib's `Equiv.Perm`,
  whose product is in operator order: a generator is read as `op` of its
  permutation of the positions (`semP`), a circuit then as `op` of its own
  (`lift_semP`, with `perm_at`).
-/
import QCert.Alt16RevCir.Theory
import QCert.Alt16RevCir.Lib.Morphism
import QCert.Alt16RevCir.Lib.Symmetric

namespace QCert.Alt16RevCir.BySymmetric

open QCert QCert.Circuit CircuitProp
open Symmetric (SG SymRel)

/-! ## The step -/

/-- The data and the hypotheses of the step (the parameters of the Agda's
module `Step`). -/
structure Step (k N : ℕ) where
  /-- the translations -/
  Θ : ℕ → Circ k
  f : Gn k → Word (SG N)
  /-- the numbering of the states -/
  enc : Fin N → Bits k
  dec : Bits k → Fin N
  dec_enc : ∀ i, dec (enc i) = i
  enc_dec : ∀ x, enc (dec x) = x
  /-- the Coxeter relations between the `Θ d`, from the rules -/
  order : ∀ d, 2 + d ≤ N → k ⊢ᵀ Θ d * Θ d ≈ 1
  braid : ∀ d, 3 + d ≤ N → k ⊢ᵀ Θ d * Θ (d + 1) * Θ d ≈ Θ (d + 1) * Θ d * Θ (d + 1)
  far : ∀ d e, 2 + d ≤ e → 2 + e ≤ N → k ⊢ᵀ Θ e * Θ d ≈ Θ d * Θ e
  /-- each gate is the circuit of its word, from the rules -/
  gate : ∀ x : Gn k, k ⊢ᵀ FreeMonoid.of x ≈ FreeMonoid.lift (fun y : SG N => Θ y.1) (f x)
  /-- the semantics of the translations -/
  f_sem_gen : ∀ (x : Gn k) (i : Fin N), Symmetric.perm (f x) i = dec (semG x (enc i))
  g_sem_gen : ∀ (y : SG N) (i : Fin N),
    dec (sem (Θ y.1) (enc i)) = Symmetric.perm (FreeMonoid.of y) i

namespace Step

variable {k N : ℕ} (S : Step k N)

/-- A transposition as a circuit. -/
def g (y : SG N) : Circ k := S.Θ y.1

/-! ### A word in the transpositions and the function of a circuit -/

theorem f_sem (w : Circ k) (i : Fin N) :
    Symmetric.perm (FreeMonoid.lift S.f w) i = S.dec (sem w (S.enc i)) := by
  induction w using FreeMonoid.inductionOn' generalizing i with
  | one => exact (S.dec_enc i).symm
  | mul_of x w ih =>
    rw [map_mul, FreeMonoid.lift_eval_of, Symmetric.perm_mul_apply, ih, S.f_sem_gen, S.enc_dec,
      sem_mul, sem_of]

/-! ### Symmetric's relations, read through `g` -/

theorem lemma_g_rel : ∀ {u t : Word (SG N)}, SymRel N u t →
    k ⊢ᵀ FreeMonoid.lift S.g u ≈ FreeMonoid.lift S.g t
  | _, _, .order d q => by
    simp only [map_mul, map_one, FreeMonoid.lift_eval_of]
    exact S.order d q
  | _, _, .braid d q => by
    simp only [map_mul, FreeMonoid.lift_eval_of]
    exact S.braid d q
  | _, _, .far d e lo q => by
    simp only [map_mul, FreeMonoid.lift_eval_of]
    exact (S.far d e lo q).symm

/-! ### The isomorphism -/

/-- `f`: circuits → words in the transpositions.  A rule equates two
circuits with the same function on states, so their words have the same
permutation, and are equal by completeness. -/
theorem f_well_defined {w v : Circ k} (r : VRel TRel k w v) :
    Derivable (SymRel N) (FreeMonoid.lift S.f w) (FreeMonoid.lift S.f v) :=
  Symmetric.complete fun i =>
    (S.f_sem w i).trans ((congrArg S.dec (T_ax_sound r (S.enc i))).trans (S.f_sem v i).symm)

/-- `g`: words in the transpositions → circuits.  Each instance of a Coxeter
relation is one between the `Θ d`. -/
theorem g_well_defined {u t : Word (SG N)} (r : SymRel N u t) :
    k ⊢ᵀ FreeMonoid.lift S.g u ≈ FreeMonoid.lift S.g t :=
  S.lemma_g_rel r

/-- A transposition and the word of its circuit have the same
permutation. -/
theorem f_left_inv_gen (y : SG N) :
    Derivable (SymRel N) (FreeMonoid.of y) (FreeMonoid.lift S.f (S.g y)) :=
  Symmetric.complete fun i => (S.g_sem_gen y i).symm.trans (S.f_sem (S.g y) i).symm

theorem g_left_inv_gen (x : Gn k) : k ⊢ᵀ FreeMonoid.of x ≈ FreeMonoid.lift S.g (S.f x) :=
  S.gate x

/-- The four facts. -/
theorem rsStep : Morphism.RSStep (VRel TRel k) (SymRel N) S.f S.g where
  f_well_defined := S.f_well_defined
  f_left_inv_gen := S.f_left_inv_gen
  g_well_defined := S.g_well_defined
  g_left_inv_gen := S.g_left_inv_gen

include S in
/-- Group-likeness, transported: the inverse of a gate `x` is the circuit of
the inverse, in Symmetric's word group, of the word of `x`. -/
theorem grouplike : Grouplike (VRel TRel k) :=
  S.rsStep.grouplike Symmetric.presentation.grouplike

/-- The circuits modulo the rules and the words in the transpositions modulo
the Coxeter relations are isomorphic, by `f ʷ`. -/
def Theorem_Circuits_iso_Transpositions :
    (conGen (VRel TRel k)).Quotient ≃* (conGen (SymRel N)).Quotient :=
  S.rsStep.iso

/-! ### The presentation, and completeness for functions on states -/

/-- The permutation of the positions of a circuit: that of its word. -/
def perm (w : Circ k) : Equiv.Perm (Fin N) := Symmetric.perm (FreeMonoid.lift S.f w)

/-- It carries the position of a state to the position of the state the
circuit sends it to. -/
theorem perm_at (w : Circ k) (i : Fin N) : S.perm w i = S.dec (sem w (S.enc i)) :=
  S.f_sem w i

include S in
/-- Two circuits with the same function on states are equal by the rules. -/
theorem complete {w v : Circ k} (e : sem w ≐ sem v) : k ⊢ᵀ w ≈ v :=
  S.rsStep.injective (Symmetric.complete fun i =>
    (S.f_sem w i).trans ((congrArg S.dec (e (S.enc i))).trans (S.f_sem v i).symm))

/-- The semantics of a generator, in the opposite of Mathlib's symmetric
group (the Agda's diagram-order `Permutation′-group N`). -/
def semP (x : Gn k) : (Equiv.Perm (Fin N))ᵐᵒᵖ := MulOpposite.op (S.perm (FreeMonoid.of x))

private theorem perm_cong {w v : Circ k} (d : k ⊢ᵀ w ≈ v) : S.perm w = S.perm v :=
  Equiv.ext fun i =>
    (S.perm_at w i).trans ((congrArg S.dec (T_sound d (S.enc i))).trans (S.perm_at v i).symm)

/-- The isomorphism, followed by Symmetric's: the rules present the
permutations of the `N` states. -/
theorem presentation : IsPresentationOf (VRel TRel k) S.semP :=
  Morphism.presentation_of S.grouplike S.perm (by rw [perm, map_one]; rfl)
    (fun a b => by
      rw [perm, map_mul, Symmetric.perm_mul]; rfl)
    (fun d => S.perm_cong d)
    (fun {a b} e => S.complete fun x => by
      have h := congrArg (fun π : Equiv.Perm (Fin N) => S.enc (π (S.dec x))) e
      simpa only [perm_at, S.enc_dec] using h)
    (fun π => ⟨FreeMonoid.lift S.g (Symmetric.go N π), Equiv.ext fun i =>
      (Symmetric.sound (S.rsStep.right_inv (Symmetric.go N π)) i).symm.trans
        (Symmetric.go_sem N π i)⟩)

/-- A circuit is read as `op` of its permutation of the positions. -/
theorem lift_semP (w : Circ k) : FreeMonoid.lift S.semP w = MulOpposite.op (S.perm w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, perm, map_one]; rfl
  | mul_of x w ih =>
    rw [map_mul, ih, FreeMonoid.lift_eval_of, semP, ← MulOpposite.op_mul]
    congr 1
    rw [perm, perm, perm, map_mul, Symmetric.perm_mul]; rfl

end Step

end QCert.Alt16RevCir.BySymmetric
