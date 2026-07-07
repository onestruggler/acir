------------------------------------------------------------------------
-- The Agda standard library
--
-- Epimorphisms (surjective homomorphisms) of monoid-like structures
--
-- The standard library has monomorphisms and isomorphisms but not
-- epimorphisms.  (Staged in ForStdlib for upstreaming into the
-- MonoidMorphisms module of Algebra.Morphism.Structures.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module ForStdlib.Algebra.Morphism.Structures where

open import Algebra.Bundles.Raw using (RawMonoid)
import Algebra.Morphism.Structures as Structures
open import Function.Definitions using (Surjective)
open import Level using (Level ; _⊔_)

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Morphisms over monoid-like structures

module MonoidMorphisms (M₁ : RawMonoid a ℓ₁) (M₂ : RawMonoid b ℓ₂) where

  open RawMonoid M₁ using () renaming (Carrier to A ; _≈_ to _≈₁_)
  open RawMonoid M₂ using () renaming (Carrier to B ; _≈_ to _≈₂_)
  open Structures.MonoidMorphisms M₁ M₂ using (IsMonoidHomomorphism)

  record IsMonoidEpimorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧
      surjective           : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsMonoidHomomorphism isMonoidHomomorphism public
