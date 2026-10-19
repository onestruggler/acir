------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules with the schema are complete on three wires, and so at
-- every width given completeness on four to twelve wires.
--
-- On three wires completeness is Natural's (Natural/ThreeWire), carried
-- over by Converse; on at most two it is Small's.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Three where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)

open import Examples.Groups.CCX+HH.NaturalP.EveryWidth using (Complete ; every-width)
open import Examples.Groups.CCX+HH.NaturalP.Converse using (complete⇐Σ)
open import Examples.Groups.CCX+HH.NaturalP.Small using (complete₀ ; complete₁ ; complete₂)
import Examples.Groups.CCX+HH.Natural.ThreeWire.Complete as W3

complete₃ : Complete 3
complete₃ = complete⇐Σ W3.complete

-- Every width, given the widths from four to twelve.
every-width₄ : (∀ {n} → 4 ≤ n → n ≤ 12 → Complete n) → ∀ n → Complete n
every-width₄ h = every-width base
  where
  base : ∀ {n} → n ≤ 12 → Complete n
  base {zero}                    _  = complete₀
  base {suc zero}                _  = complete₁
  base {suc (suc zero)}          _  = complete₂
  base {suc (suc (suc zero))}    _  = complete₃
  base {suc (suc (suc (suc n)))} le = h (s≤s (s≤s (s≤s (s≤s z≤n)))) le
