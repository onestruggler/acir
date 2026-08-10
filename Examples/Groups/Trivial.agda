------------------------------------------------------------------------
-- Presentations of groups
--
-- Two presentations of the trivial group: the empty alphabet with no
-- axioms, and an arbitrary alphabet with the universal relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial where

open import Algebra.Bundles using (Monoid ; Group)
import Algebra.Construct.Terminal as Terminal
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Unit using (⊤ ; tt)
open import Function.Definitions using (Surjective)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Normalization.NormalForm.Propositional as NFBase
open import Normalization.NormalForm.Setoid using (UniqueNormalForm)
open import Normalization.StarPresentation using (module GroupSem)
import Presentation.Base as PB
open import Presentation.Construct.Base
  using (EmptyRel ; TrivialRel ; ≈ε)
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)
open import Presentation.GroupLike using (Grouplike)
open import Presentation.Morphism using (module StarIsomorphism)
import Presentation.Properties as PP
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ)

open NFBase using (NormalForm ; NormalFormInjective)


------------------------------------------------------------------------
-- Presentations that collapse every generator

-- Both presentations below are trivial for one and the same reason:
-- every generator is already ≈-equal to ε.  All of the content of the
-- file is proved once here, from that single hypothesis.
module Collapsed
  {A : Set} (Γ : WRel A)
  (gen≈ε : ∀ x → PB._≈_ Γ [ x ]ʷ ε)
  where

  open PB Γ using (_≈_)
  open _≈_

  -- Every word collapses to ε: generators by hypothesis, ε by
  -- reflexivity, and a product by congruence followed by left-unit.
  w≈ε : ∀ {w} → w ≈ ε
  w≈ε {[ x ]ʷ} = gen≈ε x
  w≈ε {ε}      = refl
  w≈ε {w • v}  = trans (cong (w≈ε {w}) (w≈ε {v})) left-unit

  -- The normal form: every word is sent to the unique element of ⊤.
  nf : Word A → ⊤
  nf _ = tt

  nf-cong : ∀ {w v} → w ≈ v → nf w ≡ nf v
  nf-cong _ = Eq.refl

  -- Injectivity carries all the content: any two words are ≈-equal,
  -- both being ≈-equal to ε.
  nf-injective : ∀ {w v} → nf w ≡ nf v → w ≈ v
  nf-injective _ = trans w≈ε (sym w≈ε)

  nfp : NormalFormInjective Γ ⊤
  nfp = record
    { injection = record
        { to        = nf
        ; cong      = nf-cong
        ; injective = nf-injective
        }
    }

  -- The same normal form with a section: the unique normal form is
  -- realised by ε.
  nfp' : NormalForm Γ ⊤
  nfp' = record
    { rightInverse = record
        { to        = nf
        ; from      = λ _ → ε
        ; to-cong   = nf-cong
        ; from-cong = λ { Eq.refl → refl }
        ; inverseʳ  = λ { Eq.refl → sym w≈ε }
        }
    }


  -- Γ presents the trivial group.
  module Presentation where

    -- The target is the trivial (terminal) group, whose carrier is ⊤
    -- and whose equality relates every pair of elements.
    gp : Group 0ℓ 0ℓ
    gp = Terminal.group

    -- The unique semantics: every generator denotes the identity.
    ⟦_⟧₀ : A → Group.Carrier gp
    ⟦_⟧₀ _ = Group.ε gp

    module GS = GroupSem Γ (Eq.setoid ⊤) gp ⟦_⟧₀

    -- Every axiom is respected: the target group's equality is trivial.
    fʷ-cong-ax : ∀ {w v} → Γ w v → Group._≈_ gp GS.⟦ w ⟧ GS.⟦ v ⟧
    fʷ-cong-ax _ = _

    -- Group-like: ε left-inverts every generator, since [ x ]ʷ ≈ ε.
    grouplike : Grouplike Γ
    grouplike x = ε , trans left-unit (gen≈ε x)

    -- Any two normal forms coincide: ⊤ has a single element, so the
    -- separation hypothesis is discharged by η for ⊤.
    unfp :
      UniqueNormalForm Γ (Eq.setoid ⊤) (Group.setoid gp) GS.⟦_⟧ nfp'
    unfp = record { unique = λ _ → Eq.refl }

    subpresentation : Γ IsSubPresentationOf gp
    subpresentation =
      GS.GetSubPresentation.groupSubPres fʷ-cong-ax grouplike nfp' unfp

    presentation : Γ IsPresentationOf gp
    presentation = isPresentationOf subpresentation claim
      where
      claim : Surjective _≈_ (Group._≈_ gp) GS.⟦_⟧
      claim y = ε , λ _ → _


------------------------------------------------------------------------
-- The trivial group over the empty alphabet

-- ⟨ ⊥ ∣ ⟩: no generators, hence no axioms are needed.
module Empty where

  pres : WRel ⊥
  pres = EmptyRel

  open PB pres using (_≈_)

  -- Vacuously: the alphabet ⊥ has no generators.
  gen≈ε : ∀ (x : ⊥) → [ x ]ʷ ≈ ε
  gen≈ε ()

  open Collapsed pres gen≈ε public


------------------------------------------------------------------------
-- The trivial group via the universal relation

-- ⟨ A ∣ w = ε for every word w ⟩: an arbitrary alphabet, with the
-- coarsest relation TrivialRel killing every generator.
module Universal (A : Set) where

  pres : WRel A
  pres = TrivialRel

  open PB pres using (_≈_)

  -- Each generator is killed by an axiom.
  gen≈ε : ∀ (x : A) → [ x ]ʷ ≈ ε
  gen≈ε x = _≈_.axiom ≈ε

  open Collapsed pres gen≈ε public


------------------------------------------------------------------------
-- The two presentations are isomorphic

-- For any alphabet B, the presentations ⟨ ⊥ ∣ ⟩ and ⟨ B ∣ w = ε ⟩
-- present isomorphic monoids.
module Empty≅Universal (B : Set) where

  open PB (EmptyRel {⊥}) using ()
    renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PB (TrivialRel {B}) using ()
    renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PP (EmptyRel {⊥})   using () renaming (•-ε-monoid to m₁)
  open PP (TrivialRel {B}) using () renaming (•-ε-monoid to m₂)

  -- The generator map out of the empty alphabet.
  f : ⊥ → Word B
  f ()

  -- The generator map collapsing every generator to ε.
  g : B → Word ⊥
  g _ = ε

  -- (f ʷ) respects the empty relation EmptyRel, vacuously.
  f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v
  f-well-defined ()

  -- f is a left inverse of g on generators: (f ʷ) (g x) = ε ≈₂ [ x ]ʷ.
  f-left-inv-gen : ∀ (x : B) → [ x ]ʷ ≈₂ (f ʷ) (g x)
  f-left-inv-gen x = _≈₂_.axiom ≈ε

  -- (g ʷ) respects the universal relation TrivialRel: its value is a
  -- word over ⊥, and every such word is ≈₁-equal to ε.
  g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t
  g-well-defined ≈ε = Empty.w≈ε

  -- g is a left inverse of f on generators, vacuously.
  g-left-inv-gen : ∀ (x : ⊥) → [ x ]ʷ ≈₁ (g ʷ) (f x)
  g-left-inv-gen ()

  module Iso = StarIsomorphism (EmptyRel {⊥}) (TrivialRel {B}) f g
    f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen

  -- The main theorem: (f ʷ) is a monoid isomorphism between the two
  -- presented monoids.
  iso : MonoidMorphisms.IsMonoidIsomorphism
          (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂) (f ʷ)
  iso = Iso.isMonoidIsomorphism
