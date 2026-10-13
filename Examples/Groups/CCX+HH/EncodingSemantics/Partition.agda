------------------------------------------------------------------------
-- Presentations of groups
--
-- Two increasing, disjoint blocks covering a finite set of coordinates.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.EncodingSemantics.Partition where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Relation.Binary.PropositionalEquality

open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; ι)

record Partition (m n : ℕ) : Set where
  field
    left right : Emb m n
    locate : Fin n → Fin m ⊎ Fin m
    locate-left : ∀ x → locate (ι left x) ≡ inj₁ x
    locate-right : ∀ x → locate (ι right x) ≡ inj₂ x
    cover : ∀ x → [ ι left , ι right ]′ (locate x) ≡ x

  disjoint : ∀ x y → ι left x ≢ ι right y
  disjoint x y eq with trans (sym (locate-left x))
    (trans (cong locate eq) (locate-right y))
  ... | ()

open Partition public
