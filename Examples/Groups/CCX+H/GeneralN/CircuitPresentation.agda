------------------------------------------------------------------------
-- Presentations of groups
--
-- Unconditional exact matrix soundness and completeness for X,CX,CCX,H
-- circuits at every width >= 4, by Clément's subgroup translation.
-- Axioms are decoded source equations and generator recovery words.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+H.GeneralN.CircuitPresentation (n : ℕ) where

import Examples.Groups.CCX+H.CircuitTranslation as Translation
import Examples.Groups.CCX+H.GeneralN.Decoding as Decoding

open Translation.Complete n (Decoding.decoder n) public
  using (_===_ ; _≈_ ; decoded ; recover ; sound ; complete)
