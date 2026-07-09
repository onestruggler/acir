------------------------------------------------------------------------
-- Presentations of groups
--
-- This file collects main theorems for convenience.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Algebra.Bundles using (Group)

import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP
open import Relation.Binary.PropositionalEquality as Eq
open import Function.Definitions using (Congruent ; Injective)
open import Relation.Binary.Bundles using (Setoid)

open import Presentation.Definitions using (_IsPresentationOf_)

module Examples.Groups.Cyclic.Theorems where

open import Examples.Groups.Cyclic.Normalization
open import Examples.Groups.Cyclic.Semantics
import Examples.Groups.Cyclic.Soundness as LS
import Examples.Groups.Cyclic.Completeness as LC
import Examples.Groups.Cyclic.Uniqueness as LU
import Examples.Groups.Cyclic.Presentation as LP

open import Notations using (₁₊)

------------------------------------------------------------------------
-- Unique normal form, soundness, completeness and presentation

unique-nf : ∀ n →

  NFBase.UniqueNormalForm (n Cn,_===_) (NF n) (Eq.setoid (Cn n)) (⟦_⟧ {n}) (nfp' n)

unique-nf = LU.unique-nf

soundness : ∀ n →
  let
  module PPV = PP (n Cn,_===_)
  Syn        = PPV.word-setoid
  Sem        = Eq.setoid (Cn n)
  in

  Congruent (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧

soundness n = LS.sound

completeness : ∀ n →
  let
  module PPV = PP (n Cn,_===_)
  Syn        = PPV.word-setoid
  Sem        = Eq.setoid (Cn n)
  in

  Injective (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧

completeness = LC.completeness

presentation : ∀ {n} → (₁₊ n Cn,_===_) IsPresentationOf (Cn-group (₁₊ n))
presentation = LP.presentation
