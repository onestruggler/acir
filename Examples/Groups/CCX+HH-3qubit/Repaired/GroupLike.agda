------------------------------------------------------------------------
-- Presentations of groups
--
-- Adding the retained K definition preserves the inverse witnesses.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.GroupLike where

open import Data.Product.Base using (_,_)
open import Presentation.GroupLike using (Grouplike)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
import Examples.Groups.CCX+HH-3qubit.GroupLike as Original

grouplike : Grouplike _===_
grouplike g = inverse , lift proof
  where
  inverse = Data.Product.Base.proj₁ (Original.grouplike g)
  proof = Data.Product.Base.proj₂ (Original.grouplike g)
