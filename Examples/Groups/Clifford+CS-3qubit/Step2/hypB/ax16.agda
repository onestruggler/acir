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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax16 where

  lemma-[16] : ∀ {j k} {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (K jk • i k ^ 3) === (g ʷ) (i k • K jk • i k • K jk)
  lemma-[16] {jk = ₀₁} = symm (axiom [S11])
  lemma-[16] {jk = ₀₂} = by-basis-change (X₁₂) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₀₃} = by-basis-change (X₁₃) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₀₄} = by-basis-change (X₁₄) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₀₅} = by-basis-change (X₁₅) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₀₆} = by-basis-change (X₁₆) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₀₇} = by-basis-change (X₁₇) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₁₂} = by-basis-change (X₁₂ • X₀₁) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₁₃} = by-basis-change (X₁₃ • X₀₁) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₁₄} = by-basis-change (X₁₄ • X₀₁) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₁₅} = by-basis-change (X₁₅ • X₀₁) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₁₆} = by-basis-change (X₁₆ • X₀₁) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₁₇} = by-basis-change (X₁₇ • X₀₁) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₂₃} = by-basis-change (X₁₃ • X₀₁ • X₁₂) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₂₄} = by-basis-change (X₁₄ • X₀₁ • X₁₂) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₂₅} = by-basis-change (X₁₅ • X₀₁ • X₁₂) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₂₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₂₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₃₄} = by-basis-change (X₁₄ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₃₅} = by-basis-change (X₁₅ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₃₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₃₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₄₅} = by-basis-change (X₁₅ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₄₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₄₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₅₆} = by-basis-change (X₁₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₅₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S11])) 100 auto
  lemma-[16] {jk = ₆₇} = by-basis-change (X₁₇ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆) (symm (axiom [S11])) 100 auto
