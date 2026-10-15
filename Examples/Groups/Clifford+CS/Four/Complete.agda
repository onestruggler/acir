------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on four qubits
--
-- The back-and-forth argument of Section8 at width 4: the decoding
-- respects the rules of P′ (Lemma 8.8, Four.Hybrid) and inverts the
-- encoding (Lemma 8.7, Lemma87.Four), and the rules of P′ are complete
-- (Theorem410), so two four-qubit circuits with the same matrix are
-- equal by the rules of Syntactics.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Complete where

open import Data.Nat using (ℕ ; suc ; _≤_ ; s≤s)

open import Examples.Groups.Clifford+CS.Completeness
  using (Complete ; complete₀ ; complete₁ ; complete₂ ; complete₃)
open import Examples.Groups.Clifford+CS.Decoding 0 using (d)
import Examples.Groups.Clifford+CS.Section8 as Section8
open import Examples.Groups.Clifford+CS.Four.Hybrid using (dwd₄)
open import Examples.Groups.Clifford+CS.Lemma87.Four using (d∘e₄)

complete₄ : Complete 4
complete₄ = Section8.Complete′.complete 0 d dwd₄ d∘e₄

-- Completeness on up to four qubits.
complete≤₄ : ∀ {n} → n ≤ 4 → Complete n
complete≤₄ {0} _ = complete₀
complete≤₄ {1} _ = complete₁
complete≤₄ {2} _ = complete₂
complete≤₄ {3} _ = complete₃
complete≤₄ {4} _ = complete₄
complete≤₄ {suc (suc (suc (suc (suc n))))} (s≤s (s≤s (s≤s (s≤s ()))))
