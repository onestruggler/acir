------------------------------------------------------------------------
-- Presentations of groups
--
-- Trivial group presentations (empty generator set, universal relation)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Presentation.Groups.Trivial where

open import Algebra.Bundles using (Monoid)
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
import Normalization.Base as NFBase
open NFBase using (NormalFormWithoutInverse ; NormalForm)

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
  nfp : NormalFormWithoutInverse EmptyRel
  nfp = record
    { NF           = ⊤
    ; nf           = f
    ; nf-cong      = λ {w} {v} z → Eq.refl
    ; nf-injective = f-inj
    }

  -- Normal form with inverse: the unique normal form maps back to ε.
  nfp' : NormalForm EmptyRel
  nfp' = record
    { NF           = ⊤
    ; nf           = f
    ; nf-cong      = λ {w} {v} z → Eq.refl
    ; inv-nf       = λ z → ε
    ; inv-nf∘nf=id = λ {w} → sym singleton
    }

------------------------------------------------------------------------
-- The trivial group via the universal relation

-- Presentation of the trivial group over an arbitrary alphabet A,
-- using the universal relation TrivialRel equating every word with ε.
module P2 (A : Set) where

  -- The universal relation over the alphabet A.
  pres : WRel A
  pres = TrivialRel

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
  nfp : NormalFormWithoutInverse TrivialRel
  nfp = record
    { NF           = ⊤
    ; nf           = f
    ; nf-cong      = λ {w} {v} z → Eq.refl
    ; nf-injective = f-inj
    }

  -- Normal form with inverse: the unique normal form maps back to ε.
  nfp' : NormalForm TrivialRel
  nfp' = record
    { NF           = ⊤
    ; nf           = f
    ; nf-cong      = λ {w} {v} z → Eq.refl
    ; inv-nf       = λ z → ε
    ; inv-nf∘nf=id = λ {w} → sym singleton
    }

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

  -- (f *) respects the empty relation EmptyRel.
  f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v
  f-well-defined {w} {v} eq =
    _≈₂_.trans (_≈₂_.axiom ≈ε) (_≈₂_.sym (_≈₂_.axiom ≈ε))

  -- f is a left inverse of g on generators.
  f-left-inv-gen : ∀ (x : B) → [ x ]ʷ ≈₂ (f *) (g x)
  f-left-inv-gen x = _≈₂_.axiom ≈ε

  -- (g *) respects the universal relation TrivialRel.
  g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g *) u ≈₁ (g *) t
  g-well-defined {[ x ]ʷ} {t} ≈ε = _≈₁_.refl
  g-well-defined {ε} {t} ≈ε = _≈₁_.refl
  g-well-defined {u • u₁} {t} ≈ε =
    _≈₁_.trans
      (_≈₁_.cong (g-well-defined {u = u} ≈ε)
                 (g-well-defined {u = u₁} ≈ε))
      _≈₁_.left-unit

  -- g is a left inverse of f on generators, vacuously.
  g-left-inv-gen : ∀ (x : A) → [ x ]ʷ ≈₁ (g *) (f x)
  g-left-inv-gen ()

  module Iso = StarIsomorphism (EmptyRel {A}) (TrivialRel {B}) f g
    f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen

  -- The main theorem: (f *) is a monoid isomorphism between the two
  -- presented monoids.
  iso : MonoidMorphisms.IsMonoidIsomorphism
          (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂) (f *)
  iso = Iso.isMonoidIsomorphism
