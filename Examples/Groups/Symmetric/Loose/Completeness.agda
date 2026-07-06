------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the loose (endofunction) semantics of Sₙ: words
-- with equal denotations are congruent, by normalization
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)

import Normalization.Base as NFBase
import Presentation.Properties as PP
open import Presentation.Semantics

module Examples.Groups.Symmetric.Loose.Completeness where

open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)
open import Examples.Groups.Symmetric.Loose.Semantics using (Endo-setoid ; ⟦_⟧)
open import Examples.Groups.Symmetric.Loose.Soundness using (sound)
import Examples.Groups.Symmetric.Loose.Uniqueness as LU


------------------------------------------------------------------------
-- Completeness of the loose semantics

completeness : ∀ n →
  let
  module PPV = PP (n VRel,_===_)
  Syn        = PPV.word-setoid
  Sem        = Endo-setoid n
  in
  Completeness Syn Sem ⟦_⟧
completeness n =
  NFBase.by-normalization (_VRel,_===_ n) (Endo-setoid n) (⟦_⟧ {n})
    (LU.unique-nf n) sound
