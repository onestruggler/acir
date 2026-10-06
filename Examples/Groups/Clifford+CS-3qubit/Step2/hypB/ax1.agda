------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_; auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Words

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)
open TwoLevel-Less
open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified ; f ; g)
open TwoLevel-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Simplified-Lemmas
open import Examples.Groups.Clifford+CS-3qubit.Step2.Lafont-S8

open Basis-Change group-like (Rewriting.step-cong TwoLevel-Simplified-Step.X-step)

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax1 where

  lemma-[1] : ∀ {j : Index} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j ^ 4) === (g ʷ) ε

  lemma-[1] {₀} = axiom [S1]
  lemma-[1] {₁} = by-basis-change (X₀₁) (axiom [S1]) 10 auto
  lemma-[1] {₂} = by-basis-change (X₁₂ • X₀₁) (axiom [S1]) 10 auto
  lemma-[1] {₃} = by-basis-change (X₂₃ • X₁₂ • X₀₁) (axiom [S1]) 10 auto
  lemma-[1] {₄} = by-basis-change (X₃₄ • X₂₃ • X₁₂ • X₀₁) (axiom [S1]) 20 auto
  lemma-[1] {₅} = by-basis-change (X₄₅ • X₃₄ • X₂₃ • X₁₂ • X₀₁) (axiom [S1]) 20 auto
  lemma-[1] {₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂ • X₀₁) (axiom [S1]) 20 auto
  lemma-[1] {₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂ • X₀₁) (axiom [S1]) 25 auto
