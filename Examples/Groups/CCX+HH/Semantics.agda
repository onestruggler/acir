------------------------------------------------------------------------
-- Presentations of groups
--
-- Ordinary circuit matrices at every width, over the dyadic rationals.
-- The structural encoder preserves this independent tensor semantics.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Semantics where

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Structural
  isCommutativeRing-D adj-D ½ᴰ public
