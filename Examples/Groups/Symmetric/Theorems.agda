------------------------------------------------------------------------
-- Presentations of groups
--
-- This file collects main theorems for convenience.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Algebra.Bundles using (Group)

open import Presentation.Definitions
import Normalization.Base as NFBase
import Presentation.Properties as PP

module Examples.Groups.Symmetric.Theorems where

open import Examples.Groups.Symmetric.Syntactics

open SubPresentation

------------------------------------------------------------------------
-- Unique normal form, soundness, completeness and presentation

module Loose where

  open import Examples.Groups.Symmetric.Loose.Semantics
  import Examples.Groups.Symmetric.Loose.Soundness as LS
  import Examples.Groups.Symmetric.Loose.Completeness as LC
  import Examples.Groups.Symmetric.Loose.Uniqueness as LU

  unique-nf : ∀ n →
  
    NFBase.UniqueNormalForm (n VRel,_===_) (Endo-setoid n) (⟦_⟧ {n})
    
  unique-nf = LU.unique-nf

  soundness : ∀ n →
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Endo-setoid n
    in

    Soundness Syn Sem ⟦_⟧

  soundness n = LS.sound

  completeness : ∀ n →
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Endo-setoid n
    in

    Completeness Syn Sem ⟦_⟧

  completeness = LC.completeness


module Tight where

  open import Examples.Groups.Symmetric.Tight.Semantics
  import Examples.Groups.Symmetric.Tight.Soundness as TS
  import Examples.Groups.Symmetric.Tight.Completeness as TC
  import Examples.Groups.Symmetric.Tight.Uniqueness as TU
  import Examples.Groups.Symmetric.Tight.Presentation as TP

  unique-nf : ∀ n →
  
    NFBase.UniqueNormalForm (n VRel,_===_) (Group.setoid (Permutation′-group n)) (⟦_⟧ {n})
    
  unique-nf n = TU.unique-nf-tight {n}

  soundness : ∀ n →
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Group.setoid (Permutation′-group n)
    in

    Soundness Syn Sem ⟦_⟧

  soundness n = TS.sound

  completeness : ∀ n →
    let
    module PPV = PP (n VRel,_===_)
    Syn        = PPV.word-setoid
    Sem        = Group.setoid (Permutation′-group n)
    in

    Completeness Syn Sem ⟦_⟧

  completeness n = TC.completeness {n}


  presentation : ∀ n → (n VRel,_===_) IsPresentationOf (Permutation′-group n)
  presentation = TP.presentation
