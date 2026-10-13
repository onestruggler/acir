------------------------------------------------------------------------
-- Presentations of groups
--
-- Complete finite normal-form presentation of the even signed
-- permutations on eight levels, derived in the Table 1 source.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.StabilizerPresentation where

import Examples.Groups.CCX+HH.ThreeQubit.FiniteNormalization as Finite
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerNormalForm as NF
import Examples.Groups.CCX+HH.ThreeQubit.StabilizerFaithfulness as Faithful
import Examples.Groups.CCX+HH.ThreeQubit.Compact.Normalization as Normalize
import Examples.Groups.CCX+HH.ThreeQubit.Compact.Soundness as Sound
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (b)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T

open Finite (T._===_ {8}) b NF.I NF.section NF.step
  (Sound.encode-cong Normalize.initial)
  (λ g n → Sound.encode-cong (Normalize.factor g n)) Faithful.separate public
