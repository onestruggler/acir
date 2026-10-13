------------------------------------------------------------------------
-- Presentations of groups
--
-- An unconditional physical decoder for every scaled Schreier edge.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+H.GeneralN.Decoding (n : ℕ) where

import Examples.Groups.CCX+H.GeneralN.DecoderLift as Lift
import Examples.Groups.CCX+HH.GeneralN.Decoding as Dyadic

open Lift.Lift n (Dyadic.decoder n) public
  using (d ; correct) renaming (lifted to decoder)
