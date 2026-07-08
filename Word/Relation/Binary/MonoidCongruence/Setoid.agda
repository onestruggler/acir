------------------------------------------------------------------------
-- Presentations of groups
--
-- The setoid of words modulo the monoid congruence ≈
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word)

module Word.Relation.Binary.MonoidCongruence.Setoid {X : Set} (Γ : WRel X) where

open import Level using (0ℓ)
open import Relation.Binary using (Setoid)

open import Word.Relation.Binary.MonoidCongruence Γ

-- The setoid of words modulo ≈.
word-setoid : Setoid 0ℓ 0ℓ
word-setoid = record
  { Carrier       = Word X
  ; _≈_           = _≈_
  ; isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
  }
