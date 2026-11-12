------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness and completeness of a presentation's interpretation, and
-- presentations carried along a group monomorphism
--
-- The interpretation ⟦_⟧ of a sub-presentation of G is sound — words
-- equal by the relations have equal values — and complete — words with
-- equal values are equal by the relations: those are its congruence
-- and its injectivity (Sub).  A presentation is a sub-presentation
-- (subpresentation), and a group monomorphism φ : G → H carries a
-- sub-presentation of G to one of H whose interpretation is φ ∘ ⟦_⟧
-- (along): a semantics in a subgroup of H is one in H, with the same
-- soundness and completeness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.Embedding where

open import Algebra.Bundles using (Group)
import Algebra.Morphism.Construct.Composition as Compose
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Function.Base using (_∘_)
open import Level using (Level)

open import Word.Base using (WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_ ; _IsSubPresentationOf_)

private
  variable
    a b ℓ ℓ′ : Level
    X : Set

------------------------------------------------------------------------
-- Soundness and completeness

module _ {_===_ : WRel X} {G : Group a ℓ} where

  -- A presentation is a sub-presentation.
  subpresentation : _===_ IsPresentationOf G → _===_ IsSubPresentationOf G
  subpresentation p = record
    { gl   = gl
    ; ⟦_⟧  = ⟦_⟧
    ; mono = IsGroupIsomorphism.isGroupMonomorphism iso
    }
    where
    open _IsPresentationOf_ p
    open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup G)
      using (module IsGroupIsomorphism)

  -- The interpretation of a sub-presentation is sound and complete.
  module Sub (s : _===_ IsSubPresentationOf G) where

    open _IsSubPresentationOf_ s public using (⟦_⟧)
    open _IsSubPresentationOf_ s using (module GL ; mono)
    open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup G)
      using (module IsGroupMonomorphism)

    sound : ∀ {w v} → PB._≈_ _===_ w v → Group._≈_ G ⟦ w ⟧ ⟦ v ⟧
    sound = IsGroupMonomorphism.⟦⟧-cong mono

    complete : ∀ {w v} → Group._≈_ G ⟦ w ⟧ ⟦ v ⟧ → PB._≈_ _===_ w v
    complete = IsGroupMonomorphism.injective mono

  -- The same for a presentation.
  module Pres (p : _===_ IsPresentationOf G) = Sub (subpresentation p)

------------------------------------------------------------------------
-- Along a monomorphism

module _ {_===_ : WRel X} {G : Group a ℓ} {H : Group b ℓ′}
         {φ : Group.Carrier G → Group.Carrier H}
         (φ-mono : GroupMorphisms.IsGroupMonomorphism (Group.rawGroup G) (Group.rawGroup H) φ)
         where

  along : _===_ IsSubPresentationOf G → _===_ IsSubPresentationOf H
  along s = record
    { gl   = gl
    ; ⟦_⟧  = φ ∘ ⟦_⟧
    ; mono = Compose.isGroupMonomorphism {G₃ = Group.rawGroup H}
               (λ {i} {j} {k} → Group.trans H {i} {j} {k})
               {f = ⟦_⟧} {g = φ} mono φ-mono
    }
    where open _IsSubPresentationOf_ s

  along-presentation : _===_ IsPresentationOf G → _===_ IsSubPresentationOf H
  along-presentation = along ∘ subpresentation
