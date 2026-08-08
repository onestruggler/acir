------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal forms for a presented monoid, valued in a plain set B under
-- propositional equality.  This is exactly Normalization.NormalForm.Setoid
-- at the discrete setoid on B: every witness (NormalFormInjective,
-- NormalForm, BijectiveNormalForm, WeakNormalForm, UniqueNormalForm) and
-- all of their derivations are inherited unchanged.  A normal-form map's
-- congruence lands in ≡, and the section of a NormalForm is then
-- automatically congruent.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel)
open import Relation.Binary.PropositionalEquality using (setoid)

module Normalization.NormalForm.Propositional {X : Set} (Γ : WRel X) (B : Set) where

open import Normalization.NormalForm.Setoid Γ (setoid B) public
