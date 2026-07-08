------------------------------------------------------------------------
-- Presentations of groups
--
-- Core objects of a presentation Γ: the setoid of words modulo the
-- congruence ≈.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word)

module Presentation.Core {X : Set} (Γ : WRel X) where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)

open import Presentation.Base Γ

-- The setoid of words modulo the congruence ≈.
word-setoid : Setoid 0ℓ 0ℓ
word-setoid = record
  { Carrier       = Word X
  ; _≈_           = _≈_
  ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
  }
