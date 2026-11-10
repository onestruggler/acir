/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Morphisms of presentations

Translation of what `Examples/Groups/Alt16-RevCir` uses of the Agda library
modules `Presentation/Morphism.agda` (`Star-Congruence`,
`GroupMorphism.StarGroupIsomorphism`), `Presentation/MorphismId.agda` and
`Presentation/Definitions.agda` (`monoidPresentation⇒presentation`), for
the framework's words and congruences.

Two theories `Γ` over `X` and `Δ` over `Y`, and translations of their
generators into words of the other, `f : X → Word Y` and `g : Y → Word X`,
extended to words by `FreeMonoid.lift` (the Agda's `f ʷ`).  A
Reidemeister–Schreier step (`RSStep`) is four facts: each translation
carries the axioms of its source to consequences of the axioms of its
target, and the two are inverse to each other on generators.  Then the
extensions respect the congruences (`lift_cong`), they are inverse to each
other modulo them (`RSStep.left_inv`, `right_inv`), a left inverse of every
generator is carried along (`RSStep.grouplike`), and the monoids of words
modulo the two theories are isomorphic (`RSStep.iso`, the Agda's
`StarGroupIsomorphism.isGroupIsomorphism`).  For two theories over the same
alphabet with the same consequences the identity is an isomorphism
(`idIso`, the Agda's `MorphismId`).

**Deviations from the Agda.**  The Agda states that `f ʷ` is a group
isomorphism between the two word groups (setoids of words with the
congruences as equality, groups by `Grouplike`); here the isomorphism is a
`MulEquiv` of the quotient monoids `(conGen Γ).Quotient`, with `iso_mk`
saying that it is `FreeMonoid.lift f` on classes.  `presentation_of` is the
step from a reading of the words in a group to the framework's
`IsPresentationOf` in the opposite group (the Agda's groups of permutations
multiply in diagram order, Mathlib's in operator order).
-/
import QCert.Presentation
import Mathlib.Algebra.Group.Opposite

namespace QCert.Alt16RevCir.Morphism

open QCert

universe u v w

variable {X : Type u} {Y : Type v}

/-! ## The extension of a translation respects the congruences -/

/-- The Agda's `Star-Congruence.fʷ-cong`. -/
theorem lift_cong {Γ : WRel X} {Δ : WRel Y} (f : X → Word Y)
    (wd : ∀ {a b : Word X}, Γ a b → Derivable Δ (FreeMonoid.lift f a) (FreeMonoid.lift f b))
    {a b : Word X} (d : Derivable Γ a b) :
    Derivable Δ (FreeMonoid.lift f a) (FreeMonoid.lift f b) := by
  let c : Con (Word X) := (conGen Δ).comap (FreeMonoid.lift f) (map_mul _)
  have : conGen Γ ≤ c := Con.conGen_le fun _ _ r => wd r
  exact this d

/-- With a left inverse for every generator, every word has one. -/
theorem word_inv {Γ : WRel X} (gl : Grouplike Γ) (a : Word X) :
    ∃ a' : Word X, Derivable Γ (a' * a) 1 := by
  induction a using FreeMonoid.inductionOn' with
  | one => exact ⟨1, Derivable.refl _⟩
  | mul_of x a ih =>
    obtain ⟨a', ha⟩ := ih
    obtain ⟨x', hx⟩ := gl x
    refine ⟨a' * x', ?_⟩
    have h : Derivable Γ (a' * (x' * FreeMonoid.of x) * a) (a' * 1 * a) :=
      ((Derivable.refl a').mul hx).mul (Derivable.refl a)
    rw [mul_one] at h
    have e : a' * x' * (FreeMonoid.of x * a) = a' * (x' * FreeMonoid.of x) * a := by
      simp only [mul_assoc]
    rw [e]
    exact h.trans ha

/-! ## A Reidemeister–Schreier step -/

/-- The four facts of a step between `Γ` and `Δ` along `f` and `g` (the
hypotheses of the Agda's `StarGroupIsomorphism`). -/
structure RSStep (Γ : WRel X) (Δ : WRel Y) (f : X → Word Y) (g : Y → Word X) : Prop where
  f_well_defined : ∀ {a b : Word X}, Γ a b →
    Derivable Δ (FreeMonoid.lift f a) (FreeMonoid.lift f b)
  f_left_inv_gen : ∀ y : Y, Derivable Δ (FreeMonoid.of y) (FreeMonoid.lift f (g y))
  g_well_defined : ∀ {a b : Word Y}, Δ a b →
    Derivable Γ (FreeMonoid.lift g a) (FreeMonoid.lift g b)
  g_left_inv_gen : ∀ x : X, Derivable Γ (FreeMonoid.of x) (FreeMonoid.lift g (f x))

namespace RSStep

variable {Γ : WRel X} {Δ : WRel Y} {f : X → Word Y} {g : Y → Word X}

/-- Every word of `X` is the translation of its translation. -/
theorem left_inv (S : RSStep Γ Δ f g) (a : Word X) :
    Derivable Γ a (FreeMonoid.lift g (FreeMonoid.lift f a)) := by
  induction a using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of x a ih =>
    rw [map_mul, map_mul, FreeMonoid.lift_eval_of]
    exact (S.g_left_inv_gen x).mul ih

/-- Every word of `Y` is the translation of its translation. -/
theorem right_inv (S : RSStep Γ Δ f g) (b : Word Y) :
    Derivable Δ b (FreeMonoid.lift f (FreeMonoid.lift g b)) := by
  induction b using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of y b ih =>
    rw [map_mul, map_mul, FreeMonoid.lift_eval_of]
    exact (S.f_left_inv_gen y).mul ih

/-- `f ʷ` is injective modulo the congruences. -/
theorem injective (S : RSStep Γ Δ f g) {a b : Word X}
    (h : Derivable Δ (FreeMonoid.lift f a) (FreeMonoid.lift f b)) : Derivable Γ a b :=
  (S.left_inv a).trans ((lift_cong g S.g_well_defined h).trans (S.left_inv b).symm)

/-- Group-likeness, transported: the inverse of a generator `x` is the
translation of the inverse of the word of `x`. -/
theorem grouplike (S : RSStep Γ Δ f g) (gl : Grouplike Δ) : Grouplike Γ := fun x => by
  obtain ⟨b, hb⟩ := word_inv gl (f x)
  refine ⟨FreeMonoid.lift g b, ?_⟩
  have h := lift_cong g S.g_well_defined hb
  rw [map_mul, map_one] at h
  exact ((Derivable.refl _).mul (S.g_left_inv_gen x)).trans h

/-- The monoids of words modulo the two theories are isomorphic, by `f ʷ`
(the Agda's `StarGroupIsomorphism.isGroupIsomorphism`). -/
def iso (S : RSStep Γ Δ f g) : (conGen Γ).Quotient ≃* (conGen Δ).Quotient where
  toFun := Con.lift (conGen Γ) ((conGen Δ).mk'.comp (FreeMonoid.lift f)) fun _ _ h =>
    (conGen Δ).eq.2 (lift_cong f S.f_well_defined h)
  invFun := Con.lift (conGen Δ) ((conGen Γ).mk'.comp (FreeMonoid.lift g)) fun _ _ h =>
    (conGen Γ).eq.2 (lift_cong g S.g_well_defined h)
  left_inv q := by
    induction q using Con.induction_on with
    | H a => exact ((conGen Γ).eq.2 (S.left_inv a)).symm
  right_inv q := by
    induction q using Con.induction_on with
    | H b => exact ((conGen Δ).eq.2 (S.right_inv b)).symm
  map_mul' p q := map_mul _ p q

/-- The isomorphism is `f ʷ` on classes. -/
theorem iso_mk (S : RSStep Γ Δ f g) (a : Word X) :
    S.iso ((conGen Γ).mk' a) = (conGen Δ).mk' (FreeMonoid.lift f a) := rfl

end RSStep

/-! ## Two theories over one alphabet -/

/-- Two theories each of whose axioms is a consequence of the other have
the same congruence, and the identity is an isomorphism of the two monoids
of words (the Agda's `MorphismId`). -/
def idIso {Γ Δ : WRel X} (fwd : ∀ {a b : Word X}, Γ a b → Derivable Δ a b)
    (bwd : ∀ {a b : Word X}, Δ a b → Derivable Γ a b) :
    (conGen Γ).Quotient ≃* (conGen Δ).Quotient :=
  Con.congr (le_antisymm (Con.conGen_le fun _ _ r => fwd r) (Con.conGen_le fun _ _ r => bwd r))

/-! ## Presentations into the opposite of a group -/

/-- A reading `F` of the words in a group that reverses products (the words
being in diagram order), compatible with the theory, injective modulo it and
onto, gives a presentation of the opposite group, each generator read as
`op (F (of x))` (the Agda's `monoidPresentation⇒presentation`, and
`isPresentationOf`). -/
theorem presentation_of {Γ : WRel X} {G : Type w} [Group G] (gl : Grouplike Γ)
    (F : Word X → G) (F_one : F 1 = 1) (F_mul : ∀ a b, F (a * b) = F b * F a)
    (F_cong : ∀ {a b}, Derivable Γ a b → F a = F b)
    (F_inj : ∀ {a b}, F a = F b → Derivable Γ a b) (F_onto : ∀ g, ∃ a, F a = g) :
    IsPresentationOf Γ (fun x => MulOpposite.op (F (FreeMonoid.of x))) := by
  have lift_eq : ∀ a : Word X,
      FreeMonoid.lift (fun x => MulOpposite.op (F (FreeMonoid.of x))) a = MulOpposite.op (F a) := by
    intro a
    induction a using FreeMonoid.inductionOn' with
    | one => rw [map_one, F_one, MulOpposite.op_one]
    | mul_of x a ih =>
      rw [map_mul, ih, FreeMonoid.lift_eval_of, ← MulOpposite.op_mul, F_mul]
  exact
    { grouplike := gl
      sound := fun a b h => by rw [lift_eq, lift_eq, F_cong (Derivable.of h)]
      complete := fun a b h => by
        rw [lift_eq, lift_eq] at h
        exact F_inj (MulOpposite.op_injective h)
      surjective := fun g => by
        obtain ⟨a, ha⟩ := F_onto g.unop
        exact ⟨a, by rw [lift_eq, ha, MulOpposite.op_unop]⟩ }

end QCert.Alt16RevCir.Morphism
