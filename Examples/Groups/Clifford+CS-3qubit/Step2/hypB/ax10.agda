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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax10 where

  lemma-1 : TwoLevel-Simplified.Rel ⊢ i₁ • X₀₁ === X₀₁ • i₀
  lemma-1 = TR.rewrite-stl 100 auto

  lemma-2 : TwoLevel-Simplified.Rel ⊢ i₂ • X₁₂ === X₁₂ • i₁
  lemma-2 = TR.rewrite-stl 100 auto

  lemma-3 : TwoLevel-Simplified.Rel ⊢ i₃ • X₂₃ === X₂₃ • i₂
  lemma-3 = TR.rewrite-stl 100 auto

  lemma-4 : TwoLevel-Simplified.Rel ⊢ i₄ • X₃₄ === X₃₄ • i₃
  lemma-4 = TR.rewrite-stl 100 auto

  lemma-5 : TwoLevel-Simplified.Rel ⊢ i₅ • X₄₅ === X₄₅ • i₄
  lemma-5 = TR.rewrite-stl 100 auto

  lemma-6 : TwoLevel-Simplified.Rel ⊢ i₆ • X₅₆ === X₅₆ • i₅
  lemma-6 = TR.rewrite-stl 100 auto


  lemma-[10] : ∀ {j k} {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i k • X jk) === (g ʷ) (X jk • i j)
  lemma-[10] {jk = ₀₁} = TR.rewrite-stl 100 auto
  lemma-[10] {jk = ₀₂} = TR.rewrite-stl 100 auto
  lemma-[10] {jk = ₀₃} = by-basis-change (X₁₃) lemma-1 100 auto
  lemma-[10] {jk = ₀₄} = by-basis-change (X₁₄) lemma-1 100 auto
  lemma-[10] {jk = ₀₅} = by-basis-change (X₁₅) lemma-1 100 auto
  lemma-[10] {jk = ₀₆} = by-basis-change (X₁₆) lemma-1 100 auto
  lemma-[10] {jk = ₀₇} = by-basis-change (X₁₇) lemma-1 100 auto
  lemma-[10] {jk = ₁₂} = TR.rewrite-stl 100 auto
  lemma-[10] {jk = ₁₃} = by-basis-change (X₂₃) lemma-2 100 auto
  lemma-[10] {jk = ₁₄} = by-basis-change (X₂₄) lemma-2 100 auto
  lemma-[10] {jk = ₁₅} = by-basis-change (X₂₅) lemma-2 100 auto
  lemma-[10] {jk = ₁₆} = by-basis-change (X₂₆) lemma-2 100 auto
  lemma-[10] {jk = ₁₇} = by-basis-change (X₂₇) lemma-2 100 auto
  lemma-[10] {jk = ₂₃} = TR.rewrite-stl 100 auto
  lemma-[10] {jk = ₂₄} = by-basis-change (X₃₄) lemma-3 100 auto
  lemma-[10] {jk = ₂₅} = by-basis-change (X₃₅) lemma-3 100 auto
  lemma-[10] {jk = ₂₆} = by-basis-change (X₃₆) lemma-3 100 auto
  lemma-[10] {jk = ₂₇} = by-basis-change (X₃₇) lemma-3 100 auto
  lemma-[10] {jk = ₃₄} = TR.rewrite-stl 100 auto
  lemma-[10] {jk = ₃₅} = by-basis-change (X₄₅) lemma-4 100 auto
  lemma-[10] {jk = ₃₆} = by-basis-change (X₄₆) lemma-4 100 auto
  lemma-[10] {jk = ₃₇} = by-basis-change (X₄₇) lemma-4 100 auto
  lemma-[10] {jk = ₄₅} = TR.rewrite-stl 100 auto
  lemma-[10] {jk = ₄₆} = by-basis-change (X₅₆) lemma-5 100 auto
  lemma-[10] {jk = ₄₇} = by-basis-change (X₅₇) lemma-5 100 auto
  lemma-[10] {jk = ₅₆} = TR.rewrite-stl 100 auto
  lemma-[10] {jk = ₅₇} = by-basis-change (X₆₇) lemma-6 100 auto
  lemma-[10] {jk = ₆₇} = TR.rewrite-stl 100 auto
