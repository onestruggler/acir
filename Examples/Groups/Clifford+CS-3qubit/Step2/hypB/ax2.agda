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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax2 where

  lemma-[2] : ∀ {j k : Index} {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (X jk ^ 2) === (g ʷ) ε

  lemma-[2] {jk = ₀₁} = axiom [S3a]
  lemma-[2] {jk = ₀₂} = by-basis-change (X₁₂) (axiom [S3a]) 10 auto
  lemma-[2] {jk = ₀₃} = by-basis-change (X₂₃ • X₁₂) (axiom [S3a]) 10 auto
  lemma-[2] {jk = ₀₄} = by-basis-change (X₃₄ • X₂₃ • X₁₂) (axiom [S3a]) 10 auto
  lemma-[2] {jk = ₀₅} = by-basis-change (X₄₅ • X₃₄ • X₂₃ • X₁₂) (axiom [S3a]) 10 auto
  lemma-[2] {jk = ₀₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) (axiom [S3a]) 15 auto
  lemma-[2] {jk = ₀₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₂₃ • X₁₂) (axiom [S3a]) 20 auto

  lemma-[2] {jk = ₁₂} = axiom [S3b]
  lemma-[2] {jk = ₁₃} = by-basis-change (X₂₃) (axiom [S3b]) 10 auto
  lemma-[2] {jk = ₁₄} = by-basis-change (X₃₄ • X₂₃) (axiom [S3b]) 10 auto
  lemma-[2] {jk = ₁₅} = by-basis-change (X₄₅ • X₃₄ • X₂₃) (axiom [S3b]) 10 auto
  lemma-[2] {jk = ₁₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄ • X₂₃) (axiom [S3b]) 10 auto
  lemma-[2] {jk = ₁₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄ • X₂₃) (axiom [S3b]) 20 auto

  lemma-[2] {jk = ₂₃} = axiom [S3c]
  lemma-[2] {jk = ₂₄} = by-basis-change (X₃₄) (axiom [S3c]) 10 auto
  lemma-[2] {jk = ₂₅} = by-basis-change (X₄₅ • X₃₄) (axiom [S3c]) 10 auto
  lemma-[2] {jk = ₂₆} = by-basis-change (X₅₆ • X₄₅ • X₃₄) (axiom [S3c]) 10 auto
  lemma-[2] {jk = ₂₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅ • X₃₄) (axiom [S3c]) 10 auto

  lemma-[2] {jk = ₃₄} = axiom [S3d]
  lemma-[2] {jk = ₃₅} = by-basis-change (X₄₅) (axiom [S3d]) 10 auto
  lemma-[2] {jk = ₃₆} = by-basis-change (X₅₆ • X₄₅) (axiom [S3d]) 10 auto
  lemma-[2] {jk = ₃₇} = by-basis-change (X₆₇ • X₅₆ • X₄₅) (axiom [S3d]) 10 auto

  lemma-[2] {jk = ₄₅} = axiom [S3e]
  lemma-[2] {jk = ₄₆} = by-basis-change (X₅₆) (axiom [S3e]) 10 auto
  lemma-[2] {jk = ₄₇} = by-basis-change (X₆₇ • X₅₆) (axiom [S3e]) 10 auto
  lemma-[2] {jk = ₅₆} = axiom [S3f]
  lemma-[2] {jk = ₅₇} = by-basis-change (X₆₇) (axiom [S3f]) 10 auto
  lemma-[2] {jk = ₆₇} = axiom [S3g]
