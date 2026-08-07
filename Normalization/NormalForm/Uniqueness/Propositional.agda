------------------------------------------------------------------------
-- Presentations of groups
--
-- Uniqueness of normal forms valued in a plain set NF under
-- propositional equality.  This is exactly
-- Normalization.NormalForm.Uniqueness at the discrete setoid on NF:
-- UniqueNormalForm, by-normalization, by-completeness and SurjSem are
-- inherited unchanged, with the normal forms compared by ≡.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using ()

module Normalization.NormalForm.Uniqueness.Propositional
  {X : Set}
  (Γ : WRel X)
  (NF : Set)
  {c d} (Sem : Setoid c d)
  (⟦_⟧ : Word X → Setoid.Carrier Sem)
  where

