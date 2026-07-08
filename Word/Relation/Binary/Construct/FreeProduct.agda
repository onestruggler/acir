------------------------------------------------------------------------
-- Presentations of groups
--
-- The free product of presentations (the free join with no extra
-- relations) and its amalgamation: identify the two embedded images of
-- a common generating set.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Relation.Binary.Construct.FreeProduct where

open import Data.Sum using (_⊎_)

open import Word.Base
open import Word.Relation.Binary.Construct.Base

-- Free product.
infix 4 _*_
_*_ : {A B : Set} → WRel A → WRel B → WRel (A ⊎ B)
_*_  Γ Δ = Γ ⋄ Δ ⋄ EmptyRel

-- Amalgamation: identify the two embedded images of a common
-- generating set M.
data AmalgRel {M A B : Set} (f₁ : M → Word A) (f₂ : M → Word B)
    : WRel (A ⊎ B) where
  amal : ∀ {m} → AmalgRel f₁ f₂ [ (f₁ m) ]ₗ [ (f₂ m) ]ᵣ

-- Amalgamated product.
infix 4 _*_⋆_⋆_
_*_⋆_⋆_ : {M A B : Set} → WRel A → WRel B →
          (f₁ : M → Word A) → (f₂ : M → Word B) → WRel (A ⊎ B)
_*_⋆_⋆_  Γ Δ f₁ f₂ = Γ ⋄ Δ ⋄ AmalgRel f₁ f₂
