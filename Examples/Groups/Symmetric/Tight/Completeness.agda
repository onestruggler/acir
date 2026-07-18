------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the tight (permutation) semantics of Sₙ: words
-- with equal denotations are congruent, by normalization
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)

import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP
open import Function.Definitions using (Injective)
open import Relation.Binary.Bundles using (Setoid)

module Examples.Groups.Symmetric.Tight.Completeness where

open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)
open import Examples.Groups.Symmetric.Tight.Semantics using (⟦_⟧ ; Permutation′-group)
open import Examples.Groups.Symmetric.Tight.Soundness using (sound)
open import Examples.Groups.Symmetric.Normalization using (NF)
import Examples.Groups.Symmetric.Tight.Uniqueness as TU


private variable n : ℕ

------------------------------------------------------------------------
-- Completeness of the tight semantics

completeness : let open PP (n VRel,_===_) in
  Injective (Setoid._≈_ word-setoid) (Setoid._≈_ (Group.setoid (Permutation′-group n))) ⟦_⟧
completeness {n} =
  NFBase.by-normalization (_VRel,_===_ n) (NF n) (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
    TU.unique-nf-tight (sound {n})
