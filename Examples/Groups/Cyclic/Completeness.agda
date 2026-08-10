------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the cyclic group presentation: words with equal
-- denotations are congruent — the semantics ⟦_⟧ : Word X → Cn n is
-- injective on the syntactic setoid — by normalization.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Cyclic.Completeness where

open import Function.Definitions using (Injective)
open import Relation.Binary.Bundles using (Setoid)

import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP
import Relation.Binary.PropositionalEquality as Eq

open import Examples.Groups.Cyclic.Normalization using (NF ; _Cn,_===_)
open import Examples.Groups.Cyclic.Semantics using (Cn ; ⟦_⟧)
open import Examples.Groups.Cyclic.Soundness using (sound)
import Examples.Groups.Cyclic.Uniqueness as LU

------------------------------------------------------------------------
-- Completeness of the semantics

completeness : ∀ n →
  let
  module PPV = PP (n Cn,_===_)
  Syn        = PPV.word-setoid
  Sem        = Eq.setoid (Cn n)
  in
  Injective (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧
completeness n = NFBase.by-normalization
  (n Cn,_===_) (NF n) (Eq.setoid (Cn n)) (⟦_⟧ {n})
  (LU.unique-nf n) sound
