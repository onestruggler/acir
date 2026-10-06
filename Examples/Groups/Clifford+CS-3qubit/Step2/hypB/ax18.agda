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
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open Monoid-Equational
open import Presentation.Tactics.Words

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)
open TwoLevel-Less
open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified ; f ; g)
open TwoLevel-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Simplified-Lemmas
open BCu
open TRu

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax18 where

  lemma-[18] : ∀ {j k} {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (K jk ^ 2 • i j • i k) === (g ʷ) ε
  lemma-[18] {jk = ₀₁} = axiom [S14]
  lemma-[18] {jk = ₀₂} = by-basis-change (X₁₂) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₀₃} = by-basis-change (X₁₃) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₀₄} = by-basis-change (X₁₄) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₀₅} = by-basis-change (X₁₅) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₀₆} = by-basis-change (X₁₆) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₀₇} = by-basis-change (X₁₇) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₁₂} = by-basis-change (X₁₂ • X₀₁) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₁₃} = by-basis-change (X₁₃ • X₀₁) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₁₄} = by-basis-change (X₁₄ • X₀₁) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₁₅} = by-basis-change (X₁₅ • X₀₁) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₁₆} = by-basis-change (X₁₆ • X₀₁) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₁₇} = by-basis-change (X₁₇ • X₀₁) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₂₃} = by-basis-change (X₁₃ • X₀₁ • X₁₂) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₂₄} = by-basis-change (X₁₄ • X₀₁ • X₁₂) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₂₅} = by-basis-change (X₁₅ • X₀₁ • X₁₂) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₂₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₂₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₃₄} = by-basis-change (X₁₄ • X₀₁ • X₁₂ • X₂₃) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₃₅} = by-basis-change (X₁₅ • X₀₁ • X₁₂ • X₂₃) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₃₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂ • X₂₃) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₃₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₄₅} = by-basis-change (X₁₅ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₄₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₄₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₅₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₅₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (axiom [S14]) 100 auto
  lemma-[18] {jk = ₆₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆) (axiom [S14]) 100 auto
