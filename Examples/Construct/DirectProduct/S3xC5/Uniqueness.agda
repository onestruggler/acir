------------------------------------------------------------------------
-- Presentations of groups
--
-- Unique normal form for the S₃ × C₅ semantics: normal forms with
-- equal denotations in the product group are equal.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open import Notations
open import Word.Base using (Word)

module Examples.Construct.DirectProduct.S3xC5.Uniqueness where

open import Examples.Construct.DirectProduct.Sn-Sn
open import Examples.Construct.DirectProduct.S3xC5.Semantic


import Normalization.NormalForm.Propositional as NFBase


unique-nf : 
  NFBase.UniqueNormalForm (_===_) (NF n) (Eq.setoid (Cn n)) (⟦_⟧ {n}) (nfp' n)
unique-nf n = record
  { unique     = unique-lemma n
  }
