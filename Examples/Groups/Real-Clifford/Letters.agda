------------------------------------------------------------------------
-- Presentations of groups
--
-- The letters of Axioms at a fixed width, as definitions
--
-- Axioms names the letters by pattern synonyms (h₀ = gate₁ H-gate, h₁ =
-- gate₁ H-gate ↥, ...), whose constructors each carry an implicit width
-- for the elaborator to solve.  A generated derivation lists thousands
-- of letters, and from these definitions, opened at the width of the
-- equations, a list elaborates some four times faster.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Letters where

open import Data.Nat.Base using (ℕ)

open import Notations using (₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford.Syntactics

module Letters₂ (k : ℕ) where

  𝕞 h₀ h₁ z₀ z₁ c₀ : Gen (₂₊ k)
  𝕞  = gate₀ neg-gate
  h₀ = gate₁ H-gate
  h₁ = gate₁ H-gate ↥
  z₀ = gate₁ Z-gate
  z₁ = gate₁ Z-gate ↥
  c₀ = gate₂ CZ-gate

module Letters₃ (k : ℕ) where

  𝕞 h₀ h₁ h₂ z₀ z₁ z₂ c₀ c₁ : Gen (₃₊ k)
  𝕞  = gate₀ neg-gate
  h₀ = gate₁ H-gate
  h₁ = gate₁ H-gate ↥
  h₂ = gate₁ H-gate ↥ ↥
  z₀ = gate₁ Z-gate
  z₁ = gate₁ Z-gate ↥
  z₂ = gate₁ Z-gate ↥ ↥
  c₀ = gate₂ CZ-gate
  c₁ = gate₂ CZ-gate ↥
