------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness of the tight (permutation) semantics of Sₙ: words
-- with equal denotations are congruent, by normalization
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)

import Normalization.Base as NFBase
import Presentation.Properties as PP
open import Presentation.Definitions

module Examples.Groups.Symmetric.Tight.Completeness where

open import Examples.Groups.Symmetric.Syntactics using (_VRel,_===_)
open import Examples.Groups.Symmetric.Tight.Semantics using (⟦_⟧ ; Permutation′-group)
open import Examples.Groups.Symmetric.Tight.Soundness using (sound)
import Examples.Groups.Symmetric.Tight.Uniqueness as TU

open Relative


private variable n : ℕ

------------------------------------------------------------------------
-- Completeness of the tight semantics

completeness : let open PP (n VRel,_===_) in
  Completeness word-setoid (Group.setoid (Permutation′-group n)) ⟦_⟧
completeness {n} =
  NFBase.by-normalization (_VRel,_===_ n) (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
    TU.unique-nf-tight (sound {n})
