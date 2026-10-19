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

module Examples.Groups.Qubit-Clifford.Letters where

open import Data.Nat.Base using (ℕ)

open import Notations using (₃₊)
open import Examples.Groups.Qubit-Clifford.Syntactics

module Letters₃ (k : ℕ) where

  𝕨 h₀ h₁ h₂ s₀ s₁ s₂ c₀ c₁ : Gen (₃₊ k)
  𝕨  = gate₀ ω-gate
  h₀ = gate₁ H-gate
  h₁ = gate₁ H-gate ↥
  h₂ = gate₁ H-gate ↥ ↥
  s₀ = gate₁ S-gate
  s₁ = gate₁ S-gate ↥
  s₂ = gate₁ S-gate ↥ ↥
  c₀ = gate₂ CZ-gate
  c₁ = gate₂ CZ-gate ↥
