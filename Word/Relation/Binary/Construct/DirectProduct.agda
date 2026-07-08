------------------------------------------------------------------------
-- Presentations of groups
--
-- The direct product of presentations: adjoin the commutation relation
-- CommRel to the free join so that left and right generators commute.
-- _⊕^_ iterates it into an n-fold direct product.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Relation.Binary.Construct.DirectProduct where

open import Data.Nat using (ℕ ; zero)
open import Data.Sum using (_⊎_)

open import Notations
open import Word.Base
open import Word.Relation.Binary.Construct.Base

-- Commutation: left generators commute with right generators.
data CommRel {A B} : WRel (A ⊎ B) where
  comm : (a : A) (b : B) →
         CommRel ([ [ a ]ʷ ]ₗ • [ [ b ]ʷ ]ᵣ) ([ [ b ]ʷ ]ᵣ • [ [ a ]ʷ ]ₗ)

-- Direct product.
infix 4 _⊕_
_⊕_ : {A B : Set} → WRel A → WRel B → WRel (A ⊎ B)
_⊕_  Γ Δ = Γ ⋄ Δ ⋄ CommRel

-- n-fold direct product.
infix 4 _⊕^_
_⊕^_ : {A : Set} → WRel A → (n : ℕ) → WRel (A ⊎^ n)
_⊕^_ {A} Γ zero = EmptyRel
_⊕^_ {A} Γ (₁₊ zero) = Γ
_⊕^_ {A} Γ (₂₊ n) = Γ ⋄ Γ ⊕^ (₁₊ n) ⋄ CommRel
