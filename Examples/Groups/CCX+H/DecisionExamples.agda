------------------------------------------------------------------------
-- Presentations of groups
--
-- Small computations of the exact circuit decision procedure.
-- The fourth power of HX is minus identity, so it must be rejected as
-- an exact equality with the empty circuit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.DecisionExamples where

open import Data.Unit.Base using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness ; toWitnessFalse)
open import Word.Base using (ε ; _•_ ; _^_)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.Presentation as P
open import Examples.Groups.CCX+H.Decision using (_≟_)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_

  H-squared : 1 P.⊢ (H • H) ≈ ε
  H-squared = toWitness {a? = (H {0} • H) ≟ ε} tt

  X-H-do-not-commute : ¬ (1 P.⊢ (X • H) ≈ (H • X))
  X-H-do-not-commute = toWitnessFalse {a? = (X {0} • H) ≟ (H • X)} tt

  global-sign-retained : ¬ (1 P.⊢ ((H • X) ^ 4) ≈ ε)
  global-sign-retained = toWitnessFalse {a? = ((H {0} • X) ^ 4) ≟ ε} tt
