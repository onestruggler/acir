------------------------------------------------------------------------
-- Presentations of groups
--
-- Group presentations from a monoid semantics
--
-- A semantics often lands in a monoid that is not a group (scaled
-- matrices, say), so that soundness and completeness first give a
-- sub-monoid presentation.  When the relation is grouplike (every
-- generator has an inverse word) that becomes a group presentation in
-- two ways:
--
-- * units-subpresentation: every word denotes a unit of the monoid,
--   with the value of its inverse word as inverse, so the relation is a
--   sub-presentation of Units M, the group of invertible elements of M;
--
-- * Generated.presentation: the subgroup the generators generate, with
--   words as elements compared by their values (Generated.group), is
--   presented by the relation.  The group needs soundness only;
--   completeness is what makes the relation present it.
--
-- Give the monoid explicitly ({M = …}) when the expected type names
-- Units M: unifying Units ?M with it unfolds the group, which for a
-- monoid of matrices took the qutrit Clifford instance from seconds to
-- over ten minutes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.Units where

open import Algebra.Bundles using (Group ; Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Product.Base using (_,_)
open import Function.Definitions using (Injective)
open import Level using (Level ; 0ℓ ; _⊔_)
import Relation.Binary.Reasoning.Setoid as SR

import Word.Base as W
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Presentation.Definitions
  using (_IsSubMonoidPresentationOf_ ; _IsSubPresentationOf_ ; _IsPresentationOf_ ;
         subMonoidPresentation⇒subPresentation)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

private variable
  a ℓ : Level

------------------------------------------------------------------------
-- Inverses in a monoid

module Inverses (M : Monoid a ℓ) where
  open Monoid M
  open SR setoid

  -- A left inverse of x and a right inverse of an equal y are equal.
  inverse-unique : ∀ {x y x′ y′} → x′ ∙ x ≈ ε → y ∙ y′ ≈ ε → x ≈ y → x′ ≈ y′
  inverse-unique {x} {y} {x′} {y′} l r e = begin
    x′             ≈⟨ identityʳ x′ ⟨
    x′ ∙ ε         ≈⟨ ∙-congˡ r ⟨
    x′ ∙ (y ∙ y′)  ≈⟨ assoc x′ y y′ ⟨
    (x′ ∙ y) ∙ y′  ≈⟨ ∙-congʳ (∙-congˡ e) ⟨
    (x′ ∙ x) ∙ y′  ≈⟨ ∙-congʳ l ⟩
    ε ∙ y′         ≈⟨ identityˡ y′ ⟩
    y′             ∎

  -- The inverse of a product is the product of the inverses, reversed.
  product-inverse : ∀ {x y x′ y′} → x′ ∙ x ≈ ε → y′ ∙ y ≈ ε → (y′ ∙ x′) ∙ (x ∙ y) ≈ ε
  product-inverse {x} {y} {x′} {y′} l r = begin
    (y′ ∙ x′) ∙ (x ∙ y)  ≈⟨ assoc y′ x′ (x ∙ y) ⟩
    y′ ∙ (x′ ∙ (x ∙ y))  ≈⟨ ∙-congˡ (assoc x′ x y) ⟨
    y′ ∙ ((x′ ∙ x) ∙ y)  ≈⟨ ∙-congˡ (∙-congʳ l) ⟩
    y′ ∙ (ε ∙ y)         ≈⟨ ∙-congˡ (identityˡ y) ⟩
    y′ ∙ y               ≈⟨ r ⟩
    ε                    ∎

------------------------------------------------------------------------
-- The group of units of a monoid

module _ (M : Monoid a ℓ) where
  open Monoid M
  open Inverses M

  -- An element with a two-sided inverse.
  record Unit : Set (a ⊔ ℓ) where
    field
      val  : Carrier
      inv  : Carrier
      invˡ : inv ∙ val ≈ ε
      invʳ : val ∙ inv ≈ ε

  open Unit

  -- Units are compared by their values; the inverse comes along.
  Units : Group (a ⊔ ℓ) ℓ
  Units = record
    { Carrier = Unit
    ; _≈_     = λ u v → val u ≈ val v
    ; _∙_     = λ u v → record
      { val  = val u ∙ val v
      ; inv  = inv v ∙ inv u
      ; invˡ = product-inverse (invˡ u) (invˡ v)
      ; invʳ = product-inverse (invʳ v) (invʳ u)
      }
    ; ε       = record { val = ε ; inv = ε ; invˡ = identityˡ ε ; invʳ = identityˡ ε }
    ; _⁻¹     = λ u → record { val = inv u ; inv = val u ; invˡ = invʳ u ; invʳ = invˡ u }
    ; isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
            ; ∙-cong        = ∙-cong
            }
          ; assoc = λ u v w → assoc (val u) (val v) (val w)
          }
        ; identity = (λ u → identityˡ (val u)) , (λ u → identityʳ (val u))
        }
      ; inverse = invˡ , invʳ
      ; ⁻¹-cong = λ {u} {v} e → inverse-unique (invˡ u) (invʳ v) e
      }
    }

------------------------------------------------------------------------
-- A grouplike sub-monoid presentation is a sub-presentation of the units

module _ {X : Set} {_===_ : W.WRel X} {M : Monoid a ℓ}
         (smp : _===_ IsSubMonoidPresentationOf M) (gl : Grouplike _===_) where

  private
    module M = Monoid M
    open W using (Word ; _•_)
    open _IsSubMonoidPresentationOf_ smp
    open Group-Lemmas _===_ gl using (_⁻¹ ; inverseˡ ; inverseʳ)
    open MonoidMorphisms (Monoid.rawMonoid (PP.•-ε-monoid _===_)) (Monoid.rawMonoid M)
      using (IsMonoidMonomorphism)
    open IsMonoidMonomorphism mono using (⟦⟧-cong ; homo ; ε-homo ; injective)

    -- A word and its inverse word denote inverse values.
    unit : Word X → Unit M
    unit w = record
      { val  = ⟦ w ⟧
      ; inv  = ⟦ w ⁻¹ ⟧
      ; invˡ = M.trans (M.sym (homo (w ⁻¹) w)) (M.trans (⟦⟧-cong inverseˡ) ε-homo)
      ; invʳ = M.trans (M.sym (homo w (w ⁻¹))) (M.trans (⟦⟧-cong inverseʳ) ε-homo)
      }

    smpᵁ : _===_ IsSubMonoidPresentationOf Group.monoid (Units M)
    smpᵁ = record
      { ⟦_⟧  = unit
      ; mono = record
        { isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = ⟦⟧-cong }
            ; homo              = homo
            }
          ; ε-homo = ε-homo
          }
        ; injective = injective
        }
      }

  units-subpresentation : _===_ IsSubPresentationOf Units M
  units-subpresentation = subMonoidPresentation⇒subPresentation smpᵁ gl

------------------------------------------------------------------------
-- The group the generators generate, and its presentation

module Generated {X : Set} {_===_ : W.WRel X} (gl : Grouplike _===_)
                 {M : Monoid a ℓ} (⟦_⟧ : W.Word X → Monoid.Carrier M)
                 (hom : MonoidMorphisms.IsMonoidHomomorphism
                          (Monoid.rawMonoid (PP.•-ε-monoid _===_)) (Monoid.rawMonoid M) ⟦_⟧)
                 where

  private
    module M = Monoid M
    module Γ = PB _===_
    open W using (Word ; ε ; _•_)
    open Group-Lemmas _===_ gl using (_⁻¹ ; inverseˡ ; inverseʳ ; •-ε-group)
    open MonoidMorphisms.IsMonoidHomomorphism hom using (⟦⟧-cong ; homo ; ε-homo)
    open Inverses M using (inverse-unique)

    left : (w : Word X) → ⟦ w ⁻¹ ⟧ M.∙ ⟦ w ⟧ M.≈ M.ε
    left w = M.trans (M.sym (homo (w ⁻¹) w)) (M.trans (⟦⟧-cong inverseˡ) ε-homo)

    right : (w : Word X) → ⟦ w ⟧ M.∙ ⟦ w ⁻¹ ⟧ M.≈ M.ε
    right w = M.trans (M.sym (homo w (w ⁻¹))) (M.trans (⟦⟧-cong inverseʳ) ε-homo)

  -- Words, compared by their values.
  group : Group 0ℓ ℓ
  group = record
    { Carrier = Word X
    ; _≈_     = λ w v → ⟦ w ⟧ M.≈ ⟦ v ⟧
    ; _∙_     = _•_
    ; ε       = ε
    ; _⁻¹     = _⁻¹
    ; isGroup = record
      { isMonoid = record
        { isSemigroup = record
          { isMagma = record
            { isEquivalence = record { refl = M.refl ; sym = M.sym ; trans = M.trans }
            ; ∙-cong        = λ {w} {w′} {v} {v′} p q →
                M.trans (homo w v) (M.trans (M.∙-cong p q) (M.sym (homo w′ v′)))
            }
          ; assoc = λ _ _ _ → ⟦⟧-cong Γ.assoc
          }
        ; identity = (λ _ → ⟦⟧-cong Γ.left-unit) , (λ _ → ⟦⟧-cong Γ.right-unit)
        }
      ; inverse = (λ _ → ⟦⟧-cong inverseˡ) , (λ _ → ⟦⟧-cong inverseʳ)
      ; ⁻¹-cong = λ {w} {v} e → inverse-unique (left w) (right v) e
      }
    }

  -- Completeness makes the relation present it.
  presentation : Injective Γ._≈_ M._≈_ ⟦_⟧ → _===_ IsPresentationOf group
  presentation complete = record
    { gl  = gl
    ; ⟦_⟧ = λ w → w
    ; iso = record
      { isGroupMonomorphism = record
        { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism •-ε-group group record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = ⟦⟧-cong }
            ; homo              = λ _ _ → M.refl
            }
          ; ε-homo = M.refl
          }
        ; injective = complete
        }
      ; surjective = λ w → w , ⟦⟧-cong
      }
    }

-- The same, from a sub-monoid presentation.
module _ {X : Set} {_===_ : W.WRel X} {M : Monoid a ℓ}
         (smp : _===_ IsSubMonoidPresentationOf M) (gl : Grouplike _===_) where

  private
    open _IsSubMonoidPresentationOf_ smp
    open MonoidMorphisms (Monoid.rawMonoid (PP.•-ε-monoid _===_)) (Monoid.rawMonoid M)
      using (IsMonoidMonomorphism)
    open IsMonoidMonomorphism mono using (isMonoidHomomorphism ; injective)
    module G = Generated gl {M = M} ⟦_⟧ isMonoidHomomorphism

  generated : Group 0ℓ ℓ
  generated = G.group

  generated-presentation : _===_ IsPresentationOf generated
  generated-presentation = G.presentation injective
