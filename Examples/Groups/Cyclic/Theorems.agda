------------------------------------------------------------------------
-- Presentations of groups
--
-- This file collects main theorems for convenience.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}


import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP
open import Relation.Binary.PropositionalEquality as Eq
open import Function.Definitions using (Congruent ; Injective)
open import Relation.Binary.Bundles using (Setoid)

import Data.Nat.Properties as NP
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsMonoidPresentationOf_)

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

-- At order 0 the relation T ^' 0 = ε is trivial, so the presented
-- *monoid* is the free monoid on one generator, (ℕ, +, 0).  The cyclic
-- group of order 0 is ℤ, but grouplikeness fails at order 0, so the
-- monoid presentation is the sharpest statement available there.
monoid-presentation : (0 Cn,_===_) IsMonoidPresentationOf NP.+-0-monoid
monoid-presentation = LP.monoid-presentation
