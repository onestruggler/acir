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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax3 where

  lemma-[3] : ∀ {j k : Index} {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (K jk ^ 8) === ε

  lemma-[3] {jk = ₀₁} = lemma-K₀₁^8=ε
  lemma-[3] {jk = ₀₂} = by-basis-change (X₁₂) lemma-K₀₁^8=ε 10 auto
  lemma-[3] {jk = ₀₃} = by-basis-change (X₂₃ • X₁₂) lemma-K₀₁^8=ε 15 auto
  lemma-[3] {jk = ₀₄} = by-basis-change (X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 30 auto
  lemma-[3] {jk = ₀₅} = by-basis-change (X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 30 auto
  lemma-[3] {jk = ₀₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 40 auto
  lemma-[3] {jk = ₀₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 50 auto
  lemma-[3] {jk = ₁₂} = by-basis-change (X₀₁ • X₁₂) lemma-K₀₁^8=ε 15 auto
  lemma-[3] {jk = ₁₃} = by-basis-change (X₂₃ • X₀₁ • X₁₂) lemma-K₀₁^8=ε 25 auto
  lemma-[3] {jk = ₁₄} = by-basis-change (X₃₄ • X₂₃ • X₀₁ • X₁₂) lemma-K₀₁^8=ε 35 auto
  lemma-[3] {jk = ₁₅} = by-basis-change (X₄₅ • X₃₄ • X₂₃ • X₀₁ • X₁₂) lemma-K₀₁^8=ε 35 auto
  lemma-[3] {jk = ₁₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₀₁ • X₁₂) lemma-K₀₁^8=ε 50 auto
  lemma-[3] {jk = ₁₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₀₁ • X₁₂) lemma-K₀₁^8=ε 50 auto
  lemma-[3] {jk = ₂₃} = by-basis-change (X₁₂ • X₀₁ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 35 auto
  lemma-[3] {jk = ₂₄} = by-basis-change (X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 35 auto
  lemma-[3] {jk = ₂₅} = by-basis-change (X₄₅ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 50 auto
  lemma-[3] {jk = ₂₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 50 auto
  lemma-[3] {jk = ₂₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 80 auto
  lemma-[3] {jk = ₃₄} = by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 50 auto
  lemma-[3] {jk = ₃₅} = by-basis-change (X₄₅ • X₂₃ • X₁₂ • X₀₁ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 50 auto
  lemma-[3] {jk = ₃₆} = by-basis-change (X₅₆ • X₄₅ • X₂₃ • X₁₂ • X₀₁ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 70 auto
  lemma-[3] {jk = ₃₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₂₃ • X₁₂ • X₀₁ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 70 auto
  lemma-[3] {jk = ₄₅} = by-basis-change (X₃₄ • X₂₃ • X₁₂ • X₀₁ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 70 auto
  lemma-[3] {jk = ₄₆} = by-basis-change (X₅₆ • X₃₄ • X₂₃ • X₁₂ • X₀₁ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 70 auto
  lemma-[3] {jk = ₄₇} = by-basis-change (X₆₇ • X₅₆ • X₃₄ • X₂₃ • X₁₂ • X₀₁ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 70 auto
  lemma-[3] {jk = ₅₆} = by-basis-change (X₄₅ • X₃₄ • X₂₃ • X₁₂ • X₀₁ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 70 auto
  lemma-[3] {jk = ₅₇} = by-basis-change (X₆₇ • X₄₅ • X₃₄ • X₂₃ • X₁₂ • X₀₁ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 90 auto
  lemma-[3] {jk = ₆₇} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂ • X₀₁ • X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) lemma-K₀₁^8=ε 100 auto
