------------------------------------------------------------------------
-- Presentations of groups
--
-- The CCX+H rules with the schema, CCXH⁴ among them, are complete on
-- three wires (ThreeWire/Complete), and so at every width given
-- CCX+HH's on at most twelve wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Three where

open import Data.Nat.Base using (ℕ ; _≤_)

open import Examples.Groups.CCX+H.NaturalP.Complete using (Complete)
open import Examples.Groups.CCX+H.NaturalP.Small using (every-width)
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Complete public using (complete₃)
import Examples.Groups.CCX+HH.NaturalP.EveryWidth as PE

-- Every width, given CCX+HH's rules on at most twelve wires.
every-width₃ : (∀ {n} → n ≤ 12 → PE.Complete n) → ∀ n → Complete n
every-width₃ h = every-width h complete₃
