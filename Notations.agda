------------------------------------------------------------------------
-- Presentations of groups
--
-- Shared notations: numeral patterns for ℕ and Fin, and the auto
-- pattern for proofs that hold by computation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Notations where

open import Data.Fin using (zero ; suc)
open import Data.Nat using (zero ; suc)

import Relation.Binary.PropositionalEquality as Eq

-- Pattern for proofs that hold by computation.
pattern auto = Eq.refl

-- Numeral patterns, overloaded over ℕ and Fin via the shared
-- constructors zero and suc.
pattern ₀ = zero
pattern ₁ = suc ₀
pattern ₂ = suc ₁
pattern ₃ = suc ₂
pattern ₄ = suc ₃
pattern ₅ = suc ₄
pattern ₆ = suc ₅
pattern ₇ = suc ₆
pattern ₈ = suc ₇
pattern ₉ = suc ₈
pattern ₁₀ = suc ₉
pattern ₁₁ = suc ₁₀
pattern ₁₂ = suc ₁₁
pattern ₁₃ = suc ₁₂
pattern ₁₄ = suc ₁₃
pattern ₁₅ = suc ₁₄

-- Successor patterns: ₖ₊ n matches the numeral k added to n.
pattern ₁₊ ⱼ = suc ⱼ
pattern ₂₊ ⱼ = suc (suc ⱼ)
pattern ₃₊ ⱼ = suc (suc (suc ⱼ))
pattern ₄₊ ⱼ = suc (suc (suc (suc ⱼ)))
