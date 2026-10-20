------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness for affine circuits at every width, unconditionally.
--
-- `Affine` needs completeness on at most three wires only, and that
-- is proved: on zero, one and two wires by `Small`, on three by
-- `Three`.  So two affine circuits (words in X, CX and the swap) with
-- the same matrix are equal in NaturalP with the schema, at every
-- width (`affine-complete`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.AffineComplete where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; s≤s)

open import Examples.Groups.CCX+HH.NaturalP.EveryWidth using (Complete)
open import Examples.Groups.CCX+HH.NaturalP.Small using (complete₀ ; complete₁ ; complete₂)
open import Examples.Groups.CCX+HH.NaturalP.Three using (complete₃)

-- Completeness on at most three wires.
complete≤3 : ∀ {k} → k ≤ 3 → Complete k
complete≤3 {zero}                _ = complete₀
complete≤3 {suc zero}            _ = complete₁
complete≤3 {suc (suc zero)}      _ = complete₂
complete≤3 {suc (suc (suc zero))} _ = complete₃
complete≤3 {suc (suc (suc (suc k)))} (s≤s (s≤s (s≤s ())))

open import Examples.Groups.CCX+HH.NaturalP.Affine complete≤3 public
  using (affine-complete)
