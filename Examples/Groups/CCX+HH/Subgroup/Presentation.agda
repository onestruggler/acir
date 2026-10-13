------------------------------------------------------------------------
-- Presentations of groups
--
-- The index-four auxiliary subgroup, with canonical levels 0 and 1.
-- PresentationAt also accepts an arbitrary dimension with two named
-- levels, for example a symbolic power of two.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_ ; z≤n ; s≤s)

module Examples.Groups.CCX+HH.Subgroup.Presentation (N : ℕ) where

open import Notations
open import Examples.Groups.CCX+HH.Subgroup.PresentationAt
  (2 + N) ₀ ₁ (s≤s z≤n) public
