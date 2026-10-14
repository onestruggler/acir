------------------------------------------------------------------------
-- Presentations of groups
--
-- Ordinary circuit matrices at every width, over the dyadic rationals.
-- Both encoders preserve this independent tensor semantics: the
-- structural one (`encoding-correct`) and the enumeration-based one of
-- `Encoding.agda` (`enumeration-correct`), so the two agree
-- (`encoders-agree`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Semantics where

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Structural
  isCommutativeRing-D adj-D ½ᴰ public
open import Examples.Groups.CCX+HH.EncodingSemantics.Enumeration
  isCommutativeRing-D adj-D ½ᴰ public
  using (enumeration-action ; enumeration-correct ; encoders-agree)
