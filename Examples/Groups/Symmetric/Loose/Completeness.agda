------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the loose (endofunction) semantics of Sₙ: words
-- with equal denotations are congruent, by normalization
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Loose.Completeness where

open import Function.Definitions using (Injective)
open import Relation.Binary.Bundles using (Setoid)

import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP

open import Examples.Groups.Symmetric.Loose.Semantics using (Endo-setoid ; ⟦_⟧)
open import Examples.Groups.Symmetric.Loose.Soundness using (sound)
open import Examples.Groups.Symmetric.Normalization using (NF)
open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)

import Examples.Groups.Symmetric.Loose.Uniqueness as LU


------------------------------------------------------------------------
-- Completeness of the loose semantics

completeness : ∀ n →
  let
  module PPV = PP (n VRel,_===_)
  Syn        = PPV.word-setoid
  Sem        = Endo-setoid n
  in
  Injective (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧
completeness n =
  NFBase.by-normalization (_VRel,_===_ n) (NF n) (Endo-setoid n) (⟦_⟧ {n})
    (LU.unique-nf n) sound
