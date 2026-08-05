------------------------------------------------------------------------
-- Presentations of groups
--
-- Strategy B at width 2, armed: with ↑-injectivity at width 1 now a
-- theorem (Normalization.Faithful1, via the completed width-1 tower),
-- RhoExAbstract.Strategy-B yields the residual (≈) half of EVERY
-- width-2 srel-wd obligation from its coset (≡) half alone.
--
--   wd-from-coset : ∀ c {u t} → 2 QRel, u === t →
--     step 1 c u ≡ step 1 c t → act 1 c u ≋ act 1 c t
--
-- The width-2 well-definedness of the coset action is thereby reduced
-- to its coset halves — the unary families of which are already proved
-- (PushWD / PushWDM / PushWDM2 / PushWDM3).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.StrategyB2
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

import Examples.Groups.Symplectic.Normalization.Faithful1 p-2 p-prime as F1
import Examples.Groups.Symplectic.Normalization.Pushing.RhoExAbstract
  p-2 p-prime as RhoEx

-- Strategy B at n = 1: acts on width-2 words, cosets C 2.
module SB2 = RhoEx.Strategy-B 1 F1.↑-inj-↑

open SB2 public using (resid-half ; ≋-from-≈ ; wd-from-coset)
