------------------------------------------------------------------------
-- Presentations of groups
--
-- Trivial group presentations (empty generator set, universal relation)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial where

open import Algebra.Bundles using (Monoid ; Group ; AbelianGroup)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
open import Presentation.Construct.Base using (EmptyRel ; TrivialRel ; ≈ε)
open import Presentation.Morphism
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
open NFBase using (NormalFormInjective ; NormalForm)

------------------------------------------------------------------------
-- The trivial group over the empty alphabet

-- Presentation of the trivial group with the empty generator set ⊥
-- and the empty relation EmptyRel.
module P1 where
  A = ⊥

  -- The empty relation over the empty alphabet.
  pres : WRel A
  pres = EmptyRel

  open PB pres using (_≈_)
  open PP pres using (•-ε-monoid ; word-setoid)

  f : Word A → ⊤
  f _ = tt

  f-cong : ∀ {a b} → a ≈ b → f a ≡ f b
  f-cong {a} {b} eq = Eq.refl

  open _≈_

  -- Every word over the empty alphabet is ≈-equal to ε.
  singleton : ∀ {a} → a ≈ ε
  singleton {ε} = refl
  singleton {a • a₁} with singleton {a} | singleton {a₁}
  ... | ih₁ | ih₂ = trans (cong ih₁ ih₂) left-unit

  open SR word-setoid

  -- f is injective: any two words are ≈-equal via ε.
  f-inj : ∀ {a b} → f a ≡ f b → a ≈ b
  f-inj {a} {b} eq = begin
    a ≈⟨ singleton ⟩
    ε ≈⟨ sym singleton ⟩
    b ∎

  -- Normal form: the one-element type ⊤.
  nfp : NormalFormInjective EmptyRel ⊤
  nfp = record
    { injection = record
        { to        = f
        ; cong      = λ {w} {v} z → Eq.refl
        ; injective = f-inj
        }
    }

  -- Normal form with inverse: the unique normal form maps back to ε.
  nfp' : NormalForm EmptyRel ⊤
  nfp' = record
    { rightInverse = record
        { to        = f
        ; from      = λ z → ε
        ; to-cong   = λ {w} {v} z → Eq.refl
        ; from-cong = λ { Eq.refl → refl }
        ; inverseʳ  = λ { Eq.refl → sym singleton }
        }
    }

  module Presentation where

    open import Presentation.Definitions
    open import Normalization.NormalForm.Setoid
    open import Normalization.StarPresentation
    open import Presentation.GroupLike using (Grouplike)
    open import Function.Definitions using (Surjective)
    open import Data.Product using (_,_)
    open import Level
    import Algebra.Construct.Terminal as Terminal

    -- The target is the trivial (terminal) group, whose carrier is ⊤ and
    -- whose equality relates every pair of elements.
    gp : Group 0ℓ 0ℓ
    gp = Terminal.group

    -- The unique semantics out of the empty alphabet.
    ⟦_⟧₀ : A → Group.Carrier gp
    ⟦_⟧₀ ()

    module GS = GroupSem pres (Eq.setoid ⊤) gp ⟦_⟧₀

    -- Every axiom is respected, vacuously: EmptyRel has no axioms.
    fʷ-cong-ax : ∀ {w v} → pres w v → Group._≈_ gp (GS.⟦ w ⟧) (GS.⟦ v ⟧)
    fʷ-cong-ax ()

    -- Group-like, vacuously: the alphabet ⊥ has no generators.
    grouplike : Grouplike pres
    grouplike ()

    -- Any two normal forms coincide: ⊤ has a single element, so the
    -- separation hypothesis is discharged by η for ⊤.
    unfp : UniqueNormalForm pres (Eq.setoid ⊤) (Group.setoid gp) GS.⟦_⟧ nfp'
    unfp = record { unique = λ _ → Eq.refl }

    subpresentation : pres IsSubPresentationOf gp
    subpresentation =
      GS.GetSubPresentation.groupSubPres fʷ-cong-ax grouplike nfp' unfp

    presentation : pres IsPresentationOf gp
    presentation = isPresentationOf subpresentation claim
      where
      claim : Surjective _≈_ (Group._≈_ gp) GS.⟦_⟧
      claim y = ε , λ _ → _

------------------------------------------------------------------------
-- The trivial group via the universal relation

-- Presentation of the trivial group over an arbitrary alphabet A,
-- using the universal relation TrivialRel equating every word with ε.
module P2 (A : Set) where

  -- The universal relation over the alphabet A.
  pres : WRel A
  pres = TrivialRel
  infix 4 _===_
  _===_ = pres

  open PB pres using (_≈_)
  open PP pres using (•-ε-monoid ; word-setoid)

  f : Word A → ⊤
  f _ = tt

  f-cong : ∀ {a b} → a ≈ b → f a ≡ f b
  f-cong {a} {b} eq = Eq.refl

  open _≈_

  -- Every word is ≈-equal to ε.
  singleton : ∀ {a} → a ≈ ε
  singleton {ε} = refl
  singleton {[ x ]ʷ} = axiom ≈ε
  singleton {a • a₁} with singleton {a} | singleton {a₁}
  ... | ih₁ | ih₂ = trans (cong ih₁ ih₂) left-unit

  open SR word-setoid

  -- f is injective: any two words are ≈-equal via ε.
  f-inj : ∀ {a b} → f a ≡ f b → a ≈ b
  f-inj {a} {b} eq = begin
    a ≈⟨ singleton ⟩
    ε ≈⟨ sym singleton ⟩
    b ∎

  -- Normal form: the one-element type ⊤.
  nfp : NormalFormInjective TrivialRel ⊤
  nfp = record
    { injection = record
        { to        = f
        ; cong      = λ {w} {v} z → Eq.refl
        ; injective = f-inj
        }
    }

  -- Normal form with inverse: the unique normal form maps back to ε.
  nfp' : NormalForm TrivialRel ⊤
  nfp' = record
    { rightInverse = record
        { to        = f
        ; from      = λ z → ε
        ; to-cong   = λ {w} {v} z → Eq.refl
        ; from-cong = λ { Eq.refl → refl }
        ; inverseʳ  = λ { Eq.refl → sym singleton }
        }
    }


  module Presentation where

    open import Presentation.Definitions
    open import Normalization.NormalForm.Setoid
    open import Normalization.StarPresentation
    open import Presentation.GroupLike using (Grouplike)
    open import Function.Definitions using (Surjective)
    open import Data.Product using (_,_)
    open import Level
    import Algebra.Construct.Terminal as Terminal

    -- The target is the trivial (terminal) group, whose carrier is ⊤ and
    -- whose equality relates every pair of elements.
    gp : Group 0ℓ 0ℓ
    gp = Terminal.group

    -- The unique semantics collapsing every generator to the identity.
    ⟦_⟧₀ : A → Group.Carrier gp
    ⟦_⟧₀ _ = Group.ε gp

    module GS = GroupSem _===_ (Eq.setoid ⊤) gp ⟦_⟧₀

    -- Every axiom is respected: the target group's equality is trivial.
    fʷ-cong-ax : ∀ {w v} → w === v → Group._≈_ gp (GS.⟦ w ⟧) (GS.⟦ v ⟧)
    fʷ-cong-ax _ = _

    -- Group-like: ε left-inverts every generator, since [ x ]ʷ ≈ ε.
    grouplike : Grouplike _===_
    grouplike x = ε , trans left-unit (axiom ≈ε)

    -- Any two normal forms coincide: ⊤ has a single element, so the
    -- separation hypothesis is discharged by η for ⊤.
    unfp : UniqueNormalForm _===_ (Eq.setoid ⊤) (Group.setoid gp) GS.⟦_⟧ nfp'
    unfp = record { unique = λ _ → Eq.refl }

    subpresentation : (_===_) IsSubPresentationOf gp
    subpresentation =
      GS.GetSubPresentation.groupSubPres fʷ-cong-ax grouplike nfp' unfp

    presentation : _===_ IsPresentationOf gp
    presentation = isPresentationOf subpresentation claim
      where
      claim : Surjective _≈_ (Group._≈_ gp) GS.⟦_⟧
      claim y = ε , λ _ → _

------------------------------------------------------------------------
-- The two presentations are isomorphic

-- For any alphabet B, the presentations ⟨ ⊥ ∣ EmptyRel ⟩ and ⟨ B ∣ TrivialRel ⟩
-- yield isomorphic monoids.
module P1IsoP2 (B : Set) where

  A = ⊥

  open PB (EmptyRel {A}) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB (TrivialRel {B}) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP (EmptyRel {A}) renaming (•-ε-monoid to m₁)
  open PP (TrivialRel {B}) renaming (•-ε-monoid to m₂)

  -- The generator map out of the empty alphabet.
  f : A → Word B
  f ()

  -- The generator map collapsing every generator to ε.
  g : B → Word A
  g _ = ε

  -- (f ʷ) respects the empty relation EmptyRel.
  f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v
  f-well-defined {w} {v} eq =
    _≈₂_.trans (_≈₂_.axiom ≈ε) (_≈₂_.sym (_≈₂_.axiom ≈ε))

  -- f is a left inverse of g on generators.
  f-left-inv-gen : ∀ (x : B) → [ x ]ʷ ≈₂ (f ʷ) (g x)
  f-left-inv-gen x = _≈₂_.axiom ≈ε

  -- (g ʷ) respects the universal relation TrivialRel.
  g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t
  g-well-defined {[ x ]ʷ} {t} ≈ε = _≈₁_.refl
  g-well-defined {ε} {t} ≈ε = _≈₁_.refl
  g-well-defined {u • u₁} {t} ≈ε =
    _≈₁_.trans
      (_≈₁_.cong (g-well-defined {u = u} ≈ε)
                 (g-well-defined {u = u₁} ≈ε))
      _≈₁_.left-unit

  -- g is a left inverse of f on generators, vacuously.
  g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g ʷ) (f x)
  g-left-inv-gen ()

  module Iso = StarIsomorphism (EmptyRel {A}) (TrivialRel {B}) f g
    f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen

  -- The main theorem: (f ʷ) is a monoid isomorphism between the two
  -- presented monoids.
  iso : MonoidMorphisms.IsMonoidIsomorphism
          (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂) (f ʷ)
  iso = Iso.isMonoidIsomorphism
