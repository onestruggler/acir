------------------------------------------------------------------------
-- Presentations of groups
--
-- The notion "Γ presents G", in several strengths:
--
-- 1) Standard presentation (_IsPresentationOf_): _===_ presents the
--    group G iff G is isomorphic, as a group, to the free group on
--    the generators X quotiented by the congruence closure of _===_.
--
-- 2) Monoid presentation (_IsMonoidPresentationOf_): the analogous
--    notion for monoids.
--
-- 3) Sub-setoid presentation (module SubPresentation): soundness and
--    completeness of a semantics ⟦_⟧ : Syn → Sem, which together make
--    ⟦_⟧ a setoid embedding — Syn is presented as a sub-setoid of Sem.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Presentation.Definitions where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures
  using (module GroupMorphisms ; module MonoidMorphisms)
open import Level using (Level ; _⊔_)
open import Relation.Binary using (Setoid)

open import Word.Base using (WRel ; Word)

open import Presentation.GroupLike
import Presentation.Properties as PP

private variable
  a ℓ : Level
  X : Set


------------------------------------------------------------------------
-- Group presentations

-- _===_ : WRel X is a presentation of G iff there is a group
-- isomorphism ⟦_⟧ : Word X / _≈_ ≅ G, where _≈_ is the congruence
-- closure of _===_.  The source group GL.•-ε-group is (Word X, _•_,
-- ε, _⁻¹) modulo _≈_, constructed in Presentation.GroupLike from a
-- grouplike structure gl on _===_ (which gives every generator a left
-- inverse in ≈_Γ).

infix 4 _IsPresentationOf_
record _IsPresentationOf_ (_===_ : WRel X) (G : Group a ℓ) : Set (a ⊔ ℓ) where
  field
    gl : Grouplike _===_
  module GL = Group-Lemmas X _===_ gl
  open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup G)
  field
    ⟦_⟧ : Word X → Group.Carrier G
    iso : IsGroupIsomorphism ⟦_⟧

infix 4 _IsMonoidPresentationOf_
record _IsMonoidPresentationOf_ (_===_ : WRel X) (M : Monoid a ℓ) : Set (a ⊔ ℓ) where
  open MonoidMorphisms (Monoid.rawMonoid (PP.•-ε-monoid _===_)) (Monoid.rawMonoid M)
  field
    ⟦_⟧ : Word X → Monoid.Carrier M
    iso : IsMonoidIsomorphism ⟦_⟧

------------------------------------------------------------------------
-- Presentation of a sub-setoid
--
-- Soundness (⟦_⟧ preserves the equivalence) and completeness (⟦_⟧
-- reflects it) together say that ⟦_⟧ : Syn → Sem is a setoid
-- embedding: Syn is presented as the sub-setoid of Sem cut out by the
-- image of ⟦_⟧.

module SubPresentation {a b ℓ₁ ℓ₂}
  (Syn : Setoid a ℓ₁)
  (Sem : Setoid b ℓ₂)
  where

  open Setoid Syn using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid Sem using () renaming (Carrier to B; _≈_ to _≈₂_)

  Soundness : (⟦_⟧ : A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  Soundness ⟦_⟧ = ∀ {x y : A} → x ≈₁ y → ⟦ x ⟧ ≈₂ ⟦ y ⟧

  Completeness : (⟦_⟧ : A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  Completeness ⟦_⟧ = ∀ {x y : A} → ⟦ x ⟧ ≈₂ ⟦ y ⟧ → x ≈₁ y
