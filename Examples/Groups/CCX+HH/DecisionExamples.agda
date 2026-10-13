------------------------------------------------------------------------
-- Presentations of groups
--
-- Small end-to-end computations of the certified circuit decision
-- procedure, including a negative global-phase example.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.DecisionExamples where

open import Data.Unit.Base using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness ; toWitnessFalse)
open import Word.Base using (ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.Presentation as P
open import Examples.Groups.CCX+HH.Decision using (_≟_)
import Examples.Groups.CCX+HH-TwoLevel.Ring as R

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

  X-squared : (X {0} • X) P.≈ ε
  X-squared = toWitness {a? = (X {0} • X) ≟ ε} tt

  CX-squared : (CX {0} • CX) P.≈ ε
  CX-squared = toWitness {a? = (CX {0} • CX) ≟ ε} tt

  HH-squared : (HH {0} • HH) P.≈ ε
  HH-squared = toWitness {a? = (HH {0} • HH) ≟ ε} tt

  CX-HH-do-not-commute : ¬ ((CX {0} • HH) P.≈ (HH • CX))
  CX-HH-do-not-commute = toWitnessFalse {a? = (CX {0} • HH) ≟ (HH • CX)} tt

  global-sign-retained : ¬ ((minus-one {0}) P.≈ ε)
  global-sign-retained = toWitnessFalse {a? = minus-one {0} ≟ ε} tt
