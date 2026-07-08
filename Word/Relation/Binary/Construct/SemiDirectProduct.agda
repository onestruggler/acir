------------------------------------------------------------------------
-- Presentations of groups
--
-- The semi-direct product of presentations: adjoin a conjugation
-- relation, so that moving a right generator past a left generator
-- replaces the latter by its conjugate.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Relation.Binary.Construct.SemiDirectProduct where

open import Data.Sum using (_⊎_)

open import Word.Base
open import Word.Relation.Binary.Construct.Base

-- Conjugation: moving a right generator h past a left generator n
-- replaces n by its conjugate, a single generator.
data ConjRel {N H} (conj : H → N → N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) →
         ConjRel conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ)
                 ([ [ conj h n ]ʷ ]ₗ • [ [ h ]ʷ ]ᵣ)

-- Conjugation, word-valued: as ConjRel, but the conjugate of a generator
-- may be an arbitrary word over N.
data ConjRelʷ {N H} (conj : H → N → Word N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) →
         ConjRelʷ conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ)
                  ([ conj h n ]ₗ • [ [ h ]ʷ ]ᵣ)

-- Semi-direct product.
infix 4 _⋊_⋆_
_⋊_⋆_ : {N H : Set} → WRel N → WRel H → (conj : H → N → N) →
        WRel (N ⊎ H)
_⋊_⋆_  Γ Δ conj = Γ ⋄ Δ ⋄ ConjRel conj
