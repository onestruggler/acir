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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8d where

  lemma-[S7a]' : TwoLevel-Simplified.Rel ⊢ X₀₁ • K₂₃ === K₂₃ • X₀₁
  lemma-[S7a]' = by-basis-change (X₀₂ • X₁₃) (axiom [S7a]) 100 auto


  lemma-[8d] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jm : Less j m} -> {mk : Less m k} -> {lj : Less l j} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (X lm • K jk) === (g ʷ) (K jk • X lm)
  lemma-[8d] {jk = ₀₁} {₀₁} {₀₁} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₀₂} {₀₂} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₀₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₀₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₀₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₀₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₀₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₁₂} {₀₂} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₁₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₁₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₁₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₁₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₁₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₂₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₂₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₂₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₂₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₂₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₃₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₃₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₃₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₃₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₄₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₄₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₄₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₅₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₅₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₁} {₆₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₀₁} {₀₁} {₁₂} {()}
  lemma-[8d] {jk = ₀₂} {₀₂} {₀₂} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₀₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₀₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₀₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₀₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₀₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₁₂} {₀₂} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₁₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₁₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₁₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₁₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₁₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₂₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₂₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₂₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₂₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₂₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₃₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₃₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₃₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₃₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₄₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₄₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₄₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₅₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₅₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₂} {₆₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₀₁} {₀₁} {₁₃} {()}
  lemma-[8d] {jk = ₀₃} {₀₂} {₀₂} {₂₃} {()}
  lemma-[8d] {jk = ₀₃} {₀₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₀₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₀₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₀₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₀₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₁₂} {₀₂} {₂₃} {()}
  lemma-[8d] {jk = ₀₃} {₁₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₁₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₁₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₁₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₁₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₂₃} {₀₃} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₂₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₂₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₂₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₂₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₃₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₃₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₃₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₃₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₄₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₄₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₄₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₅₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₅₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₃} {₆₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₀₁} {₀₁} {₁₄} {()}
  lemma-[8d] {jk = ₀₄} {₀₂} {₀₂} {₂₄} {()}
  lemma-[8d] {jk = ₀₄} {₀₃} {₀₃} {₃₄} {()}
  lemma-[8d] {jk = ₀₄} {₀₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₀₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₀₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₀₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₁₂} {₀₂} {₂₄} {()}
  lemma-[8d] {jk = ₀₄} {₁₃} {₀₃} {₃₄} {()}
  lemma-[8d] {jk = ₀₄} {₁₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₁₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₁₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₁₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₂₃} {₀₃} {₃₄} {()}
  lemma-[8d] {jk = ₀₄} {₂₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₂₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₂₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₂₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₃₄} {₀₄} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₃₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₃₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₃₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₄₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₄₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₄₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₅₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₅₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₄} {₆₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₀₁} {₀₁} {₁₅} {()}
  lemma-[8d] {jk = ₀₅} {₀₂} {₀₂} {₂₅} {()}
  lemma-[8d] {jk = ₀₅} {₀₃} {₀₃} {₃₅} {()}
  lemma-[8d] {jk = ₀₅} {₀₄} {₀₄} {₄₅} {()}
  lemma-[8d] {jk = ₀₅} {₀₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₀₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₀₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₁₂} {₀₂} {₂₅} {()}
  lemma-[8d] {jk = ₀₅} {₁₃} {₀₃} {₃₅} {()}
  lemma-[8d] {jk = ₀₅} {₁₄} {₀₄} {₄₅} {()}
  lemma-[8d] {jk = ₀₅} {₁₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₁₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₁₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₂₃} {₀₃} {₃₅} {()}
  lemma-[8d] {jk = ₀₅} {₂₄} {₀₄} {₄₅} {()}
  lemma-[8d] {jk = ₀₅} {₂₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₂₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₂₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₃₄} {₀₄} {₄₅} {()}
  lemma-[8d] {jk = ₀₅} {₃₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₃₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₃₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₄₅} {₀₅} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₄₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₄₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₅₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₅₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₅} {₆₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₀₁} {₀₁} {₁₆} {()}
  lemma-[8d] {jk = ₀₆} {₀₂} {₀₂} {₂₆} {()}
  lemma-[8d] {jk = ₀₆} {₀₃} {₀₃} {₃₆} {()}
  lemma-[8d] {jk = ₀₆} {₀₄} {₀₄} {₄₆} {()}
  lemma-[8d] {jk = ₀₆} {₀₅} {₀₅} {₅₆} {()}
  lemma-[8d] {jk = ₀₆} {₀₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₀₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₁₂} {₀₂} {₂₆} {()}
  lemma-[8d] {jk = ₀₆} {₁₃} {₀₃} {₃₆} {()}
  lemma-[8d] {jk = ₀₆} {₁₄} {₀₄} {₄₆} {()}
  lemma-[8d] {jk = ₀₆} {₁₅} {₀₅} {₅₆} {()}
  lemma-[8d] {jk = ₀₆} {₁₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₁₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₂₃} {₀₃} {₃₆} {()}
  lemma-[8d] {jk = ₀₆} {₂₄} {₀₄} {₄₆} {()}
  lemma-[8d] {jk = ₀₆} {₂₅} {₀₅} {₅₆} {()}
  lemma-[8d] {jk = ₀₆} {₂₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₂₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₃₄} {₀₄} {₄₆} {()}
  lemma-[8d] {jk = ₀₆} {₃₅} {₀₅} {₅₆} {()}
  lemma-[8d] {jk = ₀₆} {₃₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₃₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₄₅} {₀₅} {₅₆} {()}
  lemma-[8d] {jk = ₀₆} {₄₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₄₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₅₆} {₀₆} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₅₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₆} {₆₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₇} {₀₁} {₀₁} {₁₇} {()}
  lemma-[8d] {jk = ₀₇} {₀₂} {₀₂} {₂₇} {()}
  lemma-[8d] {jk = ₀₇} {₀₃} {₀₃} {₃₇} {()}
  lemma-[8d] {jk = ₀₇} {₀₄} {₀₄} {₄₇} {()}
  lemma-[8d] {jk = ₀₇} {₀₅} {₀₅} {₅₇} {()}
  lemma-[8d] {jk = ₀₇} {₀₆} {₀₆} {₆₇} {()}
  lemma-[8d] {jk = ₀₇} {₀₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₇} {₁₂} {₀₂} {₂₇} {()}
  lemma-[8d] {jk = ₀₇} {₁₃} {₀₃} {₃₇} {()}
  lemma-[8d] {jk = ₀₇} {₁₄} {₀₄} {₄₇} {()}
  lemma-[8d] {jk = ₀₇} {₁₅} {₀₅} {₅₇} {()}
  lemma-[8d] {jk = ₀₇} {₁₆} {₀₆} {₆₇} {()}
  lemma-[8d] {jk = ₀₇} {₁₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₇} {₂₃} {₀₃} {₃₇} {()}
  lemma-[8d] {jk = ₀₇} {₂₄} {₀₄} {₄₇} {()}
  lemma-[8d] {jk = ₀₇} {₂₅} {₀₅} {₅₇} {()}
  lemma-[8d] {jk = ₀₇} {₂₆} {₀₆} {₆₇} {()}
  lemma-[8d] {jk = ₀₇} {₂₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₇} {₃₄} {₀₄} {₄₇} {()}
  lemma-[8d] {jk = ₀₇} {₃₅} {₀₅} {₅₇} {()}
  lemma-[8d] {jk = ₀₇} {₃₆} {₀₆} {₆₇} {()}
  lemma-[8d] {jk = ₀₇} {₃₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₇} {₄₅} {₀₅} {₅₇} {()}
  lemma-[8d] {jk = ₀₇} {₄₆} {₀₆} {₆₇} {()}
  lemma-[8d] {jk = ₀₇} {₄₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₇} {₅₆} {₀₆} {₆₇} {()}
  lemma-[8d] {jk = ₀₇} {₅₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₀₇} {₆₇} {₀₇} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₁₂} {₀₂} {₁₂} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₀₃} {₁₃} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₀₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₀₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₀₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₀₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₁₂} {₁₂} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₁₃} {₁₃} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₁₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₁₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₁₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₁₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₂₃} {₁₃} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₂₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₂₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₂₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₂₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₃₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₃₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₃₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₃₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₄₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₄₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₄₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₅₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₅₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₂} {₆₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₁₃} {₀₂} {₁₂} {₂₃} {₀₁} = by-basis-change (X₁₂) (lemma-[S7a]') 100 auto

  lemma-[8d] {jk = ₁₃} {₀₃} {₁₃} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₀₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₀₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₀₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₀₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₁₂} {₁₂} {₂₃} {()}
  lemma-[8d] {jk = ₁₃} {₁₃} {₁₃} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₁₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₁₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₁₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₁₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₂₃} {₁₃} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₂₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₂₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₂₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₂₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₃₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₃₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₃₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₃₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₄₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₄₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₄₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₅₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₅₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₃} {₆₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₁₄} {₀₂} {₁₂} {₂₄} {₀₁} = by-basis-change (X₁₂ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₄} {₀₃} {₁₃} {₃₄} {₀₁} = by-basis-change (X₁₂ • X₃₄ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₄} {₀₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₀₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₀₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₀₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₁₂} {₁₂} {₂₄} {()}
  lemma-[8d] {jk = ₁₄} {₁₃} {₁₃} {₃₄} {()}
  lemma-[8d] {jk = ₁₄} {₁₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₁₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₁₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₁₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₂₃} {₁₃} {₃₄} {()}
  lemma-[8d] {jk = ₁₄} {₂₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₂₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₂₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₂₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₃₄} {₁₄} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₃₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₃₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₃₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₄₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₄₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₄₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₅₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₅₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₄} {₆₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₁₅} {₀₂} {₁₂} {₂₅} {₀₁} = by-basis-change (X₁₂ • X₃₅) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₅} {₀₃} {₁₃} {₃₅} {₀₁} = by-basis-change (X₁₂ • X₃₅ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₅} {₀₄} {₁₄} {₄₅} {₀₁} = by-basis-change (X₁₂ • X₃₅ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₅} {₀₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₀₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₀₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₁₂} {₁₂} {₂₅} {()}
  lemma-[8d] {jk = ₁₅} {₁₃} {₁₃} {₃₅} {()}
  lemma-[8d] {jk = ₁₅} {₁₄} {₁₄} {₄₅} {()}
  lemma-[8d] {jk = ₁₅} {₁₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₁₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₁₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₂₃} {₁₃} {₃₅} {()}
  lemma-[8d] {jk = ₁₅} {₂₄} {₁₄} {₄₅} {()}
  lemma-[8d] {jk = ₁₅} {₂₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₂₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₂₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₃₄} {₁₄} {₄₅} {()}
  lemma-[8d] {jk = ₁₅} {₃₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₃₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₃₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₄₅} {₁₅} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₄₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₄₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₅₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₅₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₅} {₆₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₁₆} {₀₂} {₁₂} {₂₆} {₀₁} = by-basis-change (X₁₂ • X₃₆) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₆} {₀₃} {₁₃} {₃₆} {₀₁} = by-basis-change (X₁₂ • X₃₆ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₆} {₀₄} {₁₄} {₄₆} {₀₁} = by-basis-change (X₁₂ • X₃₆ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₆} {₀₅} {₁₅} {₅₆} {₀₁} = by-basis-change (X₁₂ • X₃₆ • X₂₅) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₆} {₀₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₀₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₁₂} {₁₂} {₂₆} {()}
  lemma-[8d] {jk = ₁₆} {₁₃} {₁₃} {₃₆} {()}
  lemma-[8d] {jk = ₁₆} {₁₄} {₁₄} {₄₆} {()}
  lemma-[8d] {jk = ₁₆} {₁₅} {₁₅} {₅₆} {()}
  lemma-[8d] {jk = ₁₆} {₁₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₁₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₂₃} {₁₃} {₃₆} {()}
  lemma-[8d] {jk = ₁₆} {₂₄} {₁₄} {₄₆} {()}
  lemma-[8d] {jk = ₁₆} {₂₅} {₁₅} {₅₆} {()}
  lemma-[8d] {jk = ₁₆} {₂₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₂₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₃₄} {₁₄} {₄₆} {()}
  lemma-[8d] {jk = ₁₆} {₃₅} {₁₅} {₅₆} {()}
  lemma-[8d] {jk = ₁₆} {₃₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₃₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₄₅} {₁₅} {₅₆} {()}
  lemma-[8d] {jk = ₁₆} {₄₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₄₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₅₆} {₁₆} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₅₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₆} {₆₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₇} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₁₇} {₀₂} {₁₂} {₂₇} {₀₁} = by-basis-change (X₁₂ • X₃₇) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₇} {₀₃} {₁₃} {₃₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₇} {₀₄} {₁₄} {₄₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₇} {₀₅} {₁₅} {₅₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₅) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₇} {₀₆} {₁₆} {₆₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₆) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₁₇} {₀₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₇} {₁₂} {₁₂} {₂₇} {()}
  lemma-[8d] {jk = ₁₇} {₁₃} {₁₃} {₃₇} {()}
  lemma-[8d] {jk = ₁₇} {₁₄} {₁₄} {₄₇} {()}
  lemma-[8d] {jk = ₁₇} {₁₅} {₁₅} {₅₇} {()}
  lemma-[8d] {jk = ₁₇} {₁₆} {₁₆} {₆₇} {()}
  lemma-[8d] {jk = ₁₇} {₁₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₇} {₂₃} {₁₃} {₃₇} {()}
  lemma-[8d] {jk = ₁₇} {₂₄} {₁₄} {₄₇} {()}
  lemma-[8d] {jk = ₁₇} {₂₅} {₁₅} {₅₇} {()}
  lemma-[8d] {jk = ₁₇} {₂₆} {₁₆} {₆₇} {()}
  lemma-[8d] {jk = ₁₇} {₂₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₇} {₃₄} {₁₄} {₄₇} {()}
  lemma-[8d] {jk = ₁₇} {₃₅} {₁₅} {₅₇} {()}
  lemma-[8d] {jk = ₁₇} {₃₆} {₁₆} {₆₇} {()}
  lemma-[8d] {jk = ₁₇} {₃₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₇} {₄₅} {₁₅} {₅₇} {()}
  lemma-[8d] {jk = ₁₇} {₄₆} {₁₆} {₆₇} {()}
  lemma-[8d] {jk = ₁₇} {₄₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₇} {₅₆} {₁₆} {₆₇} {()}
  lemma-[8d] {jk = ₁₇} {₅₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₁₇} {₆₇} {₁₇} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₃} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₃} {₀₃} {₂₃} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₀₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₀₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₀₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₀₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₃} {₁₃} {₂₃} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₁₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₁₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₁₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₁₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₂₃} {₂₃} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₂₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₂₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₂₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₂₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₃₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₃₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₃₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₃₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₄₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₄₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₄₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₅₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₅₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₃} {₆₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₄} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₄} {₀₃} {₂₃} {₃₄} {₀₂} = by-basis-change (X₁₂ • X₃₄ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₄} {₀₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₀₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₀₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₀₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₄} {₁₃} {₂₃} {₃₄} {₁₂} = by-basis-change (X₁₂ • X₃₄ • X₂₃ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₄} {₁₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₁₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₁₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₁₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₂₃} {₂₃} {₃₄} {()}
  lemma-[8d] {jk = ₂₄} {₂₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₂₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₂₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₂₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₃₄} {₂₄} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₃₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₃₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₃₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₄₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₄₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₄₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₅₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₅₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₄} {₆₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₅} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₅} {₀₃} {₂₃} {₃₅} {₀₂} = by-basis-change (X₁₂ • X₃₅ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₅} {₀₄} {₂₄} {₄₅} {₀₂} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₅} {₀₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₀₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₀₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₅} {₁₃} {₂₃} {₃₅} {₁₂} = by-basis-change (X₁₂ • X₃₅ • X₂₃ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₅} {₁₄} {₂₄} {₄₅} {₁₂} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₅} {₁₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₁₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₁₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₂₃} {₂₃} {₃₅} {()}
  lemma-[8d] {jk = ₂₅} {₂₄} {₂₄} {₄₅} {()}
  lemma-[8d] {jk = ₂₅} {₂₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₂₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₂₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₃₄} {₂₄} {₄₅} {()}
  lemma-[8d] {jk = ₂₅} {₃₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₃₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₃₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₄₅} {₂₅} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₄₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₄₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₅₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₅₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₅} {₆₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₆} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₆} {₀₃} {₂₃} {₃₆} {₀₂} = by-basis-change (X₁₂ • X₃₆ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₆} {₀₄} {₂₄} {₄₆} {₀₂} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₆} {₀₅} {₂₅} {₅₆} {₀₂} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₆} {₀₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₀₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₆} {₁₃} {₂₃} {₃₆} {₁₂} = by-basis-change (X₁₂ • X₃₆ • X₂₃ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₆} {₁₄} {₂₄} {₄₆} {₁₂} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₆} {₁₅} {₂₅} {₅₆} {₁₂} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₆} {₁₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₁₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₂₃} {₂₃} {₃₆} {()}
  lemma-[8d] {jk = ₂₆} {₂₄} {₂₄} {₄₆} {()}
  lemma-[8d] {jk = ₂₆} {₂₅} {₂₅} {₅₆} {()}
  lemma-[8d] {jk = ₂₆} {₂₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₂₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₃₄} {₂₄} {₄₆} {()}
  lemma-[8d] {jk = ₂₆} {₃₅} {₂₅} {₅₆} {()}
  lemma-[8d] {jk = ₂₆} {₃₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₃₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₄₅} {₂₅} {₅₆} {()}
  lemma-[8d] {jk = ₂₆} {₄₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₄₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₅₆} {₂₆} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₅₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₆} {₆₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₇} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₇} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₇} {₀₃} {₂₃} {₃₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₀₄} {₂₄} {₄₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₀₅} {₂₅} {₅₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₀₆} {₂₆} {₆₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₀₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₇} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₂₇} {₁₃} {₂₃} {₃₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₃ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₁₄} {₂₄} {₄₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₁₅} {₂₅} {₅₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₁₆} {₂₆} {₆₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₂₇} {₁₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₇} {₂₃} {₂₃} {₃₇} {()}
  lemma-[8d] {jk = ₂₇} {₂₄} {₂₄} {₄₇} {()}
  lemma-[8d] {jk = ₂₇} {₂₅} {₂₅} {₅₇} {()}
  lemma-[8d] {jk = ₂₇} {₂₆} {₂₆} {₆₇} {()}
  lemma-[8d] {jk = ₂₇} {₂₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₇} {₃₄} {₂₄} {₄₇} {()}
  lemma-[8d] {jk = ₂₇} {₃₅} {₂₅} {₅₇} {()}
  lemma-[8d] {jk = ₂₇} {₃₆} {₂₆} {₆₇} {()}
  lemma-[8d] {jk = ₂₇} {₃₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₇} {₄₅} {₂₅} {₅₇} {()}
  lemma-[8d] {jk = ₂₇} {₄₆} {₂₆} {₆₇} {()}
  lemma-[8d] {jk = ₂₇} {₄₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₇} {₅₆} {₂₆} {₆₇} {()}
  lemma-[8d] {jk = ₂₇} {₅₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₂₇} {₆₇} {₂₇} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₄} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₄} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₄} {₀₄} {₃₄} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₀₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₀₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₀₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₄} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₄} {₁₄} {₃₄} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₁₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₁₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₁₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₄} {₂₄} {₃₄} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₂₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₂₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₂₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₃₄} {₃₄} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₃₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₃₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₃₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₄₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₄₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₄₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₅₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₅₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₄} {₆₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₅} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₅} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₅} {₀₄} {₃₄} {₄₅} {₀₃} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₅} {₀₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₀₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₀₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₅} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₅} {₁₄} {₃₄} {₄₅} {₁₃} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₂₃ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₅} {₁₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₁₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₁₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₅} {₂₄} {₃₄} {₄₅} {₂₃} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₂₃ • X₀₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₅} {₂₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₂₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₂₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₃₄} {₃₄} {₄₅} {()}
  lemma-[8d] {jk = ₃₅} {₃₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₃₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₃₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₄₅} {₃₅} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₄₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₄₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₅₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₅₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₅} {₆₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₆} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₆} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₆} {₀₄} {₃₄} {₄₆} {₀₃} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₆} {₀₅} {₃₅} {₅₆} {₀₃} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₆} {₀₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₀₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₆} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₆} {₁₄} {₃₄} {₄₆} {₁₃} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₆} {₁₅} {₃₅} {₅₆} {₁₃} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₆} {₁₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₁₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₆} {₂₄} {₃₄} {₄₆} {₂₃} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃ • X₀₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₆} {₂₅} {₃₅} {₅₆} {₂₃} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃ • X₀₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₆} {₂₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₂₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₃₄} {₃₄} {₄₆} {()}
  lemma-[8d] {jk = ₃₆} {₃₅} {₃₅} {₅₆} {()}
  lemma-[8d] {jk = ₃₆} {₃₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₃₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₄₅} {₃₅} {₅₆} {()}
  lemma-[8d] {jk = ₃₆} {₄₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₄₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₅₆} {₃₆} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₅₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₆} {₆₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₇} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₇} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₇} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₇} {₀₄} {₃₄} {₄₇} {₀₃} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₀₅} {₃₅} {₅₇} {₀₃} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₀₆} {₃₆} {₆₇} {₀₃} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₀₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₇} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₇} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₇} {₁₄} {₃₄} {₄₇} {₁₃} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₁₅} {₃₅} {₅₇} {₁₃} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₁₆} {₃₆} {₆₇} {₁₃} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₁₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₇} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₃₇} {₂₄} {₃₄} {₄₇} {₂₃} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃ • X₀₁ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₂₅} {₃₅} {₅₇} {₂₃} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃ • X₀₁ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₂₆} {₃₆} {₆₇} {₂₃} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₀₁ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₃₇} {₂₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₇} {₃₄} {₃₄} {₄₇} {()}
  lemma-[8d] {jk = ₃₇} {₃₅} {₃₅} {₅₇} {()}
  lemma-[8d] {jk = ₃₇} {₃₆} {₃₆} {₆₇} {()}
  lemma-[8d] {jk = ₃₇} {₃₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₇} {₄₅} {₃₅} {₅₇} {()}
  lemma-[8d] {jk = ₃₇} {₄₆} {₃₆} {₆₇} {()}
  lemma-[8d] {jk = ₃₇} {₄₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₇} {₅₆} {₃₆} {₆₇} {()}
  lemma-[8d] {jk = ₃₇} {₅₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₃₇} {₆₇} {₃₇} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₀₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₀₅} {₄₅} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₀₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₀₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₁₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₁₅} {₄₅} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₁₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₁₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₂₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₂₅} {₄₅} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₂₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₂₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₃₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₅} {₃₅} {₄₅} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₃₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₃₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₄₅} {₄₅} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₄₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₄₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₅₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₅₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₅} {₆₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₀₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₀₅} {₄₅} {₅₆} {₀₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₆} {₀₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₀₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₁₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₁₅} {₄₅} {₅₆} {₁₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₆} {₁₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₁₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₂₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₂₅} {₄₅} {₅₆} {₂₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄ • X₀₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₆} {₂₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₂₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₃₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₆} {₃₅} {₄₅} {₅₆} {₃₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄ • X₀₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₆} {₃₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₃₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₄₅} {₄₅} {₅₆} {()}
  lemma-[8d] {jk = ₄₆} {₄₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₄₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₅₆} {₄₆} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₅₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₆} {₆₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₇} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₀₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₀₅} {₄₅} {₅₇} {₀₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₀₆} {₄₆} {₆₇} {₀₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₀₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₇} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₁₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₁₅} {₄₅} {₅₇} {₁₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₁₆} {₄₆} {₆₇} {₁₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₁₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₇} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₂₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₂₅} {₄₅} {₅₇} {₂₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄ • X₀₁ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₂₆} {₄₆} {₆₇} {₂₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄ • X₀₁ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₂₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₇} {₃₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₄₇} {₃₅} {₄₅} {₅₇} {₃₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄ • X₀₁ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₃₆} {₄₆} {₆₇} {₃₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄ • X₀₁ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₄₇} {₃₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₇} {₄₅} {₄₅} {₅₇} {()}
  lemma-[8d] {jk = ₄₇} {₄₆} {₄₆} {₆₇} {()}
  lemma-[8d] {jk = ₄₇} {₄₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₇} {₅₆} {₄₆} {₆₇} {()}
  lemma-[8d] {jk = ₄₇} {₅₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₄₇} {₆₇} {₄₇} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₀₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₀₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₀₆} {₅₆} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₀₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₁₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₁₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₁₆} {₅₆} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₁₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₂₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₂₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₂₆} {₅₆} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₂₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₃₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₃₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₃₆} {₅₆} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₃₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₄₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₆} {₄₆} {₅₆} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₄₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₅₆} {₅₆} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₅₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₆} {₆₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₇} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₀₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₀₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₀₆} {₅₆} {₆₇} {₀₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₅₇} {₀₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₇} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₁₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₁₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₁₆} {₅₆} {₆₇} {₁₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₁) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₅₇} {₁₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₇} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₂₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₂₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₂₆} {₅₆} {₆₇} {₂₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₂) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₅₇} {₂₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₇} {₃₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₃₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₃₆} {₅₆} {₆₇} {₃₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₃) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₅₇} {₃₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₇} {₄₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₅₇} {₄₆} {₅₆} {₆₇} {₄₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₄) (lemma-[S7a]') 100 auto
  lemma-[8d] {jk = ₅₇} {₄₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₇} {₅₆} {₅₆} {₆₇} {()}
  lemma-[8d] {jk = ₅₇} {₅₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₅₇} {₆₇} {₅₇} {()} {lj}
  lemma-[8d] {jk = ₆₇} {₀₁} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₀₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₀₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₀₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₀₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₀₆} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₀₇} {₆₇} {()} {lj}
  lemma-[8d] {jk = ₆₇} {₁₂} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₁₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₁₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₁₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₁₆} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₁₇} {₆₇} {()} {lj}
  lemma-[8d] {jk = ₆₇} {₂₃} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₂₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₂₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₂₆} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₂₇} {₆₇} {()} {lj}
  lemma-[8d] {jk = ₆₇} {₃₄} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₃₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₃₆} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₃₇} {₆₇} {()} {lj}
  lemma-[8d] {jk = ₆₇} {₄₅} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₄₆} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₄₇} {₆₇} {()} {lj}
  lemma-[8d] {jk = ₆₇} {₅₆} {()} {mk} {lj}
  lemma-[8d] {jk = ₆₇} {₅₇} {₆₇} {()} {lj}
  lemma-[8d] {jk = ₆₇} {₆₇} {₆₇} {()} {lj}

