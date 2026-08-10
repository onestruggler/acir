------------------------------------------------------------------------
-- Presentations of groups
--
-- The two presentations are isomorphic.
--
-- For any alphabet B, ⟨ ⊥ ∣ ⟩ (Syntactics) and ⟨ B ∣ w = ε ⟩
-- (Syntactics-Alt) present isomorphic monoids.  Both present the
-- trivial group -- Presentation and Presentation-Alt say so
-- separately -- but this is the syntactic statement, a monoid
-- isomorphism between the two presented monoids, and it does not go
-- through the semantics at all.
--
-- Each translation is forced: out of ⊥ there is nothing to say, and
-- into ⊥ every generator must go to ε.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Trivial.Presentation-Equivalence (B : Set) where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥)

open import Presentation.Construct.Base using (EmptyRel ; TrivialRel ; ≈ε)
open import Presentation.Morphism using (module StarIsomorphism)
open import Word.Base using (Word ; [_]ʷ ; ε ; _ʷ)

import Presentation.Base as PB
import Presentation.Properties as PP

import Examples.Groups.Trivial.Normalization as Nrm
import Examples.Groups.Trivial.Syntactics as Syn

private
  -- The empty side's collapse lemma, which is what makes (g ʷ)
  -- well-defined below.
  module N = Nrm Syn.pres Syn.gen≈ε

open PB (EmptyRel {⊥}) using ()
  renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
open PB (TrivialRel {B}) using ()
  renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
open PP (EmptyRel {⊥})   using () renaming (•-ε-monoid to m₁)
open PP (TrivialRel {B}) using () renaming (•-ε-monoid to m₂)

------------------------------------------------------------------------
-- The two translations

-- The generator map out of the empty alphabet.
f : ⊥ → Word B
f ()

-- The generator map collapsing every generator to ε.
g : B → Word ⊥
g _ = ε

------------------------------------------------------------------------
-- Both are well defined, and mutually inverse on generators

-- (f ʷ) respects the empty relation EmptyRel, vacuously.
f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v
f-well-defined ()

-- f is a left inverse of g on generators: (f ʷ) (g x) = ε ≈₂ [ x ]ʷ.
f-left-inv-gen : ∀ (x : B) → [ x ]ʷ ≈₂ (f ʷ) (g x)
f-left-inv-gen x = _≈₂_.axiom ≈ε

-- (g ʷ) respects the universal relation TrivialRel: its value is a
-- word over ⊥, and every such word is ≈₁-equal to ε.
g-well-defined : ∀ {u t : Word B} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t
g-well-defined ≈ε = N.w≈ε

-- g is a left inverse of f on generators, vacuously.
g-left-inv-gen : ∀ (x : ⊥) → [ x ]ʷ ≈₁ (g ʷ) (f x)
g-left-inv-gen ()

module Iso = StarIsomorphism (EmptyRel {⊥}) (TrivialRel {B}) f g
  f-well-defined f-left-inv-gen g-well-defined g-left-inv-gen

------------------------------------------------------------------------
-- The isomorphism

-- (f ʷ) is a monoid isomorphism between the two presented monoids.
iso : MonoidMorphisms.IsMonoidIsomorphism
        (Monoid.rawMonoid m₁) (Monoid.rawMonoid m₂) (f ʷ)
iso = Iso.isMonoidIsomorphism
