------------------------------------------------------------------------
-- Presentations of groups
--
-- Unconditional soundness and completeness for X,CX,CCX,HH circuits
-- at every width at least four, by Clément's subgroup translation.
-- The axioms are decoded auxiliary equations and gate recovery words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.Presentation (n : ℕ) where

import Examples.Groups.CCX+HH.CircuitTranslation as Translation
import Examples.Groups.CCX+HH.GeneralN.Decoding as Decoding

open Translation.Complete n (Decoding.decoder n) public
  using (_===_ ; _≈_ ; decoded ; recover ; sound ; complete)
