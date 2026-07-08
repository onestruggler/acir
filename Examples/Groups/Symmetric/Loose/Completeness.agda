------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the loose (endofunction) semantics of Sₙ: words
-- with equal denotations are congruent, by normalization
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}


import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP
open import Presentation.Definitions

module Examples.Groups.Symmetric.Loose.Completeness where

open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)
open import Examples.Groups.Symmetric.Loose.Semantics using (Endo-setoid ; ⟦_⟧)
open import Examples.Groups.Symmetric.Loose.Soundness using (sound)
open import Examples.Groups.Symmetric.Normalization using (NF)
import Examples.Groups.Symmetric.Loose.Uniqueness as LU

open SubPresentation


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
  NFBase.by-normalization (_VRel,_===_ n) (NF n) (Endo-setoid n) (⟦_⟧ {n})
    (LU.unique-nf n) sound
