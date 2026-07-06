{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ)
import Presentation.Properties as PP
open import Presentation.Definitions

module Examples.Groups.Symmetric.Loose.Completeness where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Cosets
open import Examples.Groups.Symmetric.Normalization using (nf-of ; NF ; inv-nf)
open import Examples.Groups.Symmetric.Loose.Semantics
open import Examples.Groups.Symmetric.Loose.Soundness
import Examples.Groups.Symmetric.Loose.Uniqueness as LU
open Relative

completeness : ∀ n →
  let
  module PPV = PP (n VRel,_===_)
  Syn        = PPV.word-setoid
  Sem        = Endo-setoid n
  in
  Completeness Syn Sem ⟦_⟧
completeness n =
  PP.by-normalization (_VRel,_===_ n) (Endo-setoid n) (⟦_⟧ {n}) (LU.unique-nf n) sound
