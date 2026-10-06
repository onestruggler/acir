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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax4 where

  lemma-[4] : ∀ {j k} -> {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j • i k) === (g ʷ) (i k • i j)

  lemma-[4] {jk = ₀₁} = symm (axiom [S4a])
  lemma-[4] {jk = ₀₂} = by-basis-change (X₁₂) (symm (axiom [S4a])) 20 auto
  lemma-[4] {jk = ₀₃} = by-basis-change (X₂₃ • X₁₂) (symm (axiom [S4a])) 15 auto
  lemma-[4] {jk = ₀₄} = by-basis-change (X₃₄ • X₂₃ • X₁₂) (symm (axiom [S4a])) 30 auto
  lemma-[4] {jk = ₀₅} = by-basis-change (X₄₅ • X₃₄ • X₂₃ • X₁₂) (symm (axiom [S4a])) 30 auto
  lemma-[4] {jk = ₀₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) (symm (axiom [S4a])) 40 auto
  lemma-[4] {jk = ₀₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) (symm (axiom [S4a])) 50 auto
  lemma-[4] {jk = ₁₂} = BC.by-basis-change (X₁₂ • X₀₁) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₁₃} = BC.by-basis-change (X₁₂ • X₂₃ • X₀₁) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₁₄} = BC.by-basis-change (X₀₁) (lemma-[4] {jk = ₀₄}) 200 auto
  lemma-[4] {jk = ₁₅} = BC.by-basis-change (X₀₁) (lemma-[4] {jk = ₀₅}) 200 auto
  lemma-[4] {jk = ₁₆} = BC.by-basis-change (X₀₁) (lemma-[4] {jk = ₀₆}) 200 auto
  lemma-[4] {jk = ₁₇} = BC.by-basis-change (X₀₁) (lemma-[4] {jk = ₀₇}) 200 auto
  lemma-[4] {jk = ₂₃} = BC.by-basis-change (X₁₂ • X₂₃ • X₀₁ • X₁₂) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₂₄} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₂₅} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₀₁ • X₁₂) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₂₆} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₂₇} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₀₁ • X₁₂) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₃₄} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₃₅} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₃₆} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₃₇} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₄₅} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₄₆} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₄₇} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₅₆} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₅₇} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S4a])) 200 auto
  lemma-[4] {jk = ₆₇} = BC.by-basis-change (X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆) (symm (axiom [S4a])) 200 auto
