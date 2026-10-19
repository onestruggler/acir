------------------------------------------------------------------------
-- Presentations of groups
--
-- The rules with the schema are complete on at most two wires, and so
-- at every width given completeness on three to twelve wires.
--
-- On no wires every circuit is ε; on one and two wires completeness is
-- Natural's (Natural/Width1, Natural/Width2), carried over by Converse.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Small where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes ; no)

open import Examples.Groups.CCX+HH.NaturalP.EveryWidth using (Complete ; every-width)
open import Examples.Groups.CCX+HH.NaturalP.Converse using (complete⇐Σ ; completeΣ₀)
import Examples.Groups.CCX+HH.Natural.Width1 as W1
import Examples.Groups.CCX+HH.Natural.Width2 as W2

complete₀ : Complete 0
complete₀ = completeΣ₀

complete₁ : Complete 1
complete₁ = complete⇐Σ W1.complete

complete₂ : Complete 2
complete₂ = complete⇐Σ W2.complete

-- Every width, given the widths from three to twelve.
every-width₃ : (∀ {n} → 3 ≤ n → n ≤ 12 → Complete n) → ∀ n → Complete n
every-width₃ h = every-width base
  where
  base : ∀ {n} → n ≤ 12 → Complete n
  base {zero}                 _  = complete₀
  base {suc zero}             _  = complete₁
  base {suc (suc zero)}       _  = complete₂
  base {suc (suc (suc n))}    le = h (s≤s (s≤s (s≤s z≤n))) le
