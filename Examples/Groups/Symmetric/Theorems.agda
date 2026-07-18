------------------------------------------------------------------------
-- Presentations of groups
--
-- This file collects main theorems for convenience.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Group)

import Normalization.NormalForm.Propositional as NFBase
import Presentation.Properties as PP
open import Presentation.Definitions using (_IsPresentationOf_)
open import Function.Definitions using (Congruent ; Injective)
open import Relation.Binary.Bundles using (Setoid)

module Examples.Groups.Symmetric.Theorems where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Normalization using (NF ; nfp'-t)

------------------------------------------------------------------------
-- Unique normal form, soundness, completeness and presentation

module Loose where

  open import Examples.Groups.Symmetric.Loose.Semantics
  import Examples.Groups.Symmetric.Loose.Soundness as LS
  import Examples.Groups.Symmetric.Loose.Completeness as LC
  import Examples.Groups.Symmetric.Loose.Uniqueness as LU

  unique-nf : ∀ n →
  
    NFBase.UniqueNormalForm (n VRel,_===_) (NF n) (Endo-setoid n) (⟦_⟧ {n}) (nfp'-t n)
    
  unique-nf = LU.unique-nf

  soundness : ∀ n →
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Endo-setoid n
    in

    Congruent (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧

  soundness n = LS.sound

  completeness : ∀ n →
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Endo-setoid n
    in

    Injective (Setoid._≈_ Syn) (Setoid._≈_ Sem) ⟦_⟧

  completeness = LC.completeness


module Tight where

  open import Examples.Groups.Symmetric.Tight.Semantics
  import Examples.Groups.Symmetric.Tight.Uniqueness as TU
  import Examples.Groups.Symmetric.Tight.Presentation as TP

  unique-nf : ∀ n →
  
    NFBase.UniqueNormalForm (n VRel,_===_) (NF n) (Group.setoid (Permutation′-group n)) (⟦_⟧ {n}) (nfp'-t n)
    
  unique-nf n = TU.unique-nf-tight {n}


  presentation : ∀ n → (n VRel,_===_) IsPresentationOf (Permutation′-group n)
  presentation n = TP.presentation {n}
