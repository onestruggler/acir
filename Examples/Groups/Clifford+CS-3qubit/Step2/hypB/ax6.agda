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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax6 where
  
  lemma-i₀-K₁₂=K₁₂-i₀ : TwoLevel-Simplified.Rel ⊢ i₀ • K₁₂ === K₁₂ • i₀
  lemma-i₀-K₁₂=K₁₂-i₀ =
    equational i₀ • K₁₂
      by by-basis-change (X₁₂ • X₀₁) ((axiom [S4b])) 200 auto
    equals K₁₂ • i₀

  lemma-[S6b] : TwoLevel-Simplified.Rel ⊢ i₀ • K₂₃ === K₂₃ • i₀
  lemma-[S6b] =
    equational i₀ • K₂₃
      by by-basis-change (X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
    equals K₂₃ • i₀

  lemma-[S6c] : TwoLevel-Simplified.Rel ⊢ i₀ • K₃₄ === K₃₄ • i₀
  lemma-[S6c] =
    equational i₀ • K₃₄
      by by-basis-change (X₃₄ • X₂₃) (lemma-[S6b]) 200 auto
    equals K₃₄ • i₀


  lemma-[S6d] : TwoLevel-Simplified.Rel ⊢ i₀ • K₄₅ === K₄₅ • i₀
  lemma-[S6d] =
    equational i₀ • K₄₅
      by by-basis-change (X₄₅ • X₃₄) (lemma-[S6c]) 200 auto
    equals K₄₅ • i₀


  lemma-[S6e] : TwoLevel-Simplified.Rel ⊢ i₀ • K₅₆ === K₅₆ • i₀
  lemma-[S6e] =
    equational i₀ • K₅₆
      by by-basis-change (X₅₆ • X₄₅) (lemma-[S6d]) 200 auto
    equals K₅₆ • i₀


  lemma-[S6f] : TwoLevel-Simplified.Rel ⊢ i₀ • K₆₇ === K₆₇ • i₀
  lemma-[S6f] =
    equational i₀ • K₆₇
      by BCr.by-basis-change (X₆₇ • X₅₆) (lemma-[S6e]) 200 auto
    equals K₆₇ • i₀


  lemma-[6a] : ∀ {j k l} {kl : Less k l} -> {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j • K kl) === (g ʷ) (K kl • i j)
  lemma-[6a] {kl = ₀₁} {()}
  lemma-[6a] {kl = ₀₂} {()}
  lemma-[6a] {kl = ₀₃} {()}
  lemma-[6a] {kl = ₀₄} {()}
  lemma-[6a] {kl = ₀₅} {()}
  lemma-[6a] {kl = ₀₆} {()}
  lemma-[6a] {kl = ₀₇} {()}
  lemma-[6a] {kl = ₁₂} {₀₁} = lemma-i₀-K₁₂=K₁₂-i₀
  lemma-[6a] {kl = ₁₃} {₀₁} = by-basis-change (X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₁₄} {₀₁} = by-basis-change (X₂₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₁₅} {₀₁} = by-basis-change (X₂₃ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₁₆} {₀₁} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₁₇} {₀₁} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₃} {₀₂} = by-basis-change (X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₃} {₁₂} = by-basis-change (X₂₃ • X₁₂ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₄} {₀₂} = by-basis-change (X₂₃ • X₃₄ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₄} {₁₂} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₅} {₀₂} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₅} {₁₂} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₆} {₀₂} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₆} {₁₂} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₇} {₀₂} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₂₇} {₁₂} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₄} {₀₃} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₄} {₁₃} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₄} {₂₃} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₅} {₀₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₅} {₁₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₀₁ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₅} {₂₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₆} {₀₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₆} {₁₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₀₁ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₆} {₂₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₇} {₀₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₇} {₁₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₀₁ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₃₇} {₂₃} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₅} {₀₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₅} {₁₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₅} {₂₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₅} {₃₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₆} {₀₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₆} {₁₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₆} {₂₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₆} {₃₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₇} {₀₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₇} {₁₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₇} {₂₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₄₇} {₃₄} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₆} {₀₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₆} {₁₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₆} {₂₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₆} {₃₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₆} {₄₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₇} {₀₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₇} {₁₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₇} {₂₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₇} {₃₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₅₇} {₄₅} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₆₇} {₀₆} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₆₇} {₁₆} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₆₇} {₂₆} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₆₇} {₃₆} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₆₇} {₄₆} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6a] {kl = ₆₇} {₅₆} = by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto


  lemma-[6b] : ∀ {j k l} {kl : Less k l} -> {lj : Less l j} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j • K kl) === (g ʷ) (K kl • i j)
  lemma-[6b] {.₂} {.₀} {.₁} {₀₁} {₁₂} = by-basis-change (X₀₁ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₃} {.₀} {.₁} {₀₁} {₁₃} = by-basis-change (X₀₁ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₄} {.₀} {.₁} {₀₁} {₁₄} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₅} {.₀} {.₁} {₀₁} {₁₅} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₀} {.₁} {₀₁} {₁₆} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₀} {.₁} {₀₁} {₁₇} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₃} {.₀} {.₂} {₀₂} {₂₃} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₄} {.₀} {.₂} {₀₂} {₂₄} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₅} {.₀} {.₂} {₀₂} {₂₅} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₀} {.₂} {₀₂} {₂₆} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₀} {.₂} {₀₂} {₂₇} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₄} {.₀} {.₃} {₀₃} {₃₄} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₅} {.₀} {.₃} {₀₃} {₃₅} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₀} {.₃} {₀₃} {₃₆} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₀} {.₃} {₀₃} {₃₇} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₅} {.₀} {.₄} {₀₄} {₄₅} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₀} {.₄} {₀₄} {₄₆} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₀} {.₄} {₀₄} {₄₇} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₀} {.₅} {₀₅} {₅₆} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₀} {.₅} {₀₅} {₅₇} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₀} {.₆} {₀₆} {₆₇} = by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {j} {.₀} {.₇} {₀₇} {()}
  lemma-[6b] {.₃} {.₁} {.₂} {₁₂} {₂₃} = by-basis-change (X₀₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₄} {.₁} {.₂} {₁₂} {₂₄} = by-basis-change (X₀₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₅} {.₁} {.₂} {₁₂} {₂₅} = by-basis-change (X₀₃ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₁} {.₂} {₁₂} {₂₆} = by-basis-change (X₀₃ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₁} {.₂} {₁₂} {₂₇} = by-basis-change (X₀₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₄} {.₁} {.₃} {₁₃} {₃₄} = by-basis-change (X₀₃ • X₃₄ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₅} {.₁} {.₃} {₁₃} {₃₅} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₁} {.₃} {₁₃} {₃₆} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₁} {.₃} {₁₃} {₃₇} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₅} {.₁} {.₄} {₁₄} {₄₅} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₁} {.₄} {₁₄} {₄₆} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₁} {.₄} {₁₄} {₄₇} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₆} {.₁} {.₅} {₁₅} {₅₆} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₁} {.₅} {₁₅} {₅₇} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {.₇} {.₁} {.₆} {₁₆} {₆₇} = by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6b] {j} {.₁} {.₇} {₁₇} {()}
  lemma-[6b] {.₄} {.₂} {.₃} {₂₃} {₃₄} = BCu.by-basis-change (X₀₄) ((lemma-[S6b])) 500 auto
  lemma-[6b] {.₅} {.₂} {.₃} {₂₃} {₃₅} = by-basis-change (X₀₄ • X₄₅) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₆} {.₂} {.₃} {₂₃} {₃₆} = by-basis-change (X₀₄ • X₄₅ • X₅₆) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₇} {.₂} {.₃} {₂₃} {₃₇} = by-basis-change (X₀₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₅} {.₂} {.₄} {₂₄} {₄₅} = by-basis-change (X₀₄ • X₄₅ • X₃₄) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₆} {.₂} {.₄} {₂₄} {₄₆} = by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₇} {.₂} {.₄} {₂₄} {₄₇} = by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₆₇) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₆} {.₂} {.₅} {₂₅} {₅₆} = by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₄₅) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₇} {.₂} {.₅} {₂₅} {₅₇} = by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇) ((lemma-[S6b])) 200 auto
  lemma-[6b] {.₇} {.₂} {.₆} {₂₆} {₆₇} = by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((lemma-[S6b])) 200 auto
  lemma-[6b] {j} {.₂} {.₇} {₂₇} {()}
  lemma-[6b] {.₅} {.₃} {.₄} {₃₄} {₄₅} = by-basis-change (X₀₅) ((lemma-[S6c])) 200 auto
  lemma-[6b] {.₆} {.₃} {.₄} {₃₄} {₄₆} = by-basis-change (X₀₅ • X₅₆) ((lemma-[S6c])) 200 auto
  lemma-[6b] {.₇} {.₃} {.₄} {₃₄} {₄₇} = by-basis-change (X₀₅ • X₅₆ • X₆₇) ((lemma-[S6c])) 200 auto
  lemma-[6b] {.₆} {.₃} {.₅} {₃₅} {₅₆} = by-basis-change (X₀₅ • X₅₆ • X₄₅) ((lemma-[S6c])) 200 auto
  lemma-[6b] {.₇} {.₃} {.₅} {₃₅} {₅₇} = by-basis-change (X₀₅ • X₅₆ • X₄₅ • X₆₇) ((lemma-[S6c])) 200 auto
  lemma-[6b] {.₇} {.₃} {.₆} {₃₆} {₆₇} = by-basis-change (X₀₅ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((lemma-[S6c])) 200 auto
  lemma-[6b] {j} {.₃} {.₇} {₃₇} {()}
  lemma-[6b] {.₆} {.₄} {.₅} {₄₅} {₅₆} = by-basis-change (X₀₆) ((lemma-[S6d])) 200 auto
  lemma-[6b] {.₇} {.₄} {.₅} {₄₅} {₅₇} = by-basis-change (X₀₆ • X₆₇) ((lemma-[S6d])) 200 auto
  lemma-[6b] {.₇} {.₄} {.₆} {₄₆} {₆₇} = by-basis-change (X₀₆ • X₆₇ • X₅₆) ((lemma-[S6d])) 200 auto
  lemma-[6b] {j} {.₄} {.₇} {₄₇} {()}
  lemma-[6b] {.₇} {.₅} {.₆} {₅₆} {₆₇} = by-basis-change (X₀₇) ((lemma-[S6e])) 400 auto
  lemma-[6b] {j} {.₅} {.₇} {₅₇} {()}
  lemma-[6b] {j} {.₆} {.₇} {₆₇} {()}


  lemma-[6c] : ∀ {j k l} {kl : Less k l} -> {kj : Less k j} -> {jl : Less j l} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j • K kl) === (g ʷ) (K kl • i j)
  lemma-[6c] {₀} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₀} {₁} {₀₁} {()} {jl}
  lemma-[6c] {₀} {₀} {₂} {₀₂} {()} {jl}
  lemma-[6c] {₀} {₀} {₃} {₀₃} {()} {jl}
  lemma-[6c] {₀} {₀} {₄} {₀₄} {()} {jl}
  lemma-[6c] {₀} {₀} {₅} {₀₅} {()} {jl}
  lemma-[6c] {₀} {₀} {₆} {₀₆} {()} {jl}
  lemma-[6c] {₀} {₀} {₇} {₀₇} {()} {jl}
  lemma-[6c] {₀} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₀} {₁} {₂} {₁₂} {()} {jl}
  lemma-[6c] {₀} {₁} {₃} {₁₃} {()} {jl}
  lemma-[6c] {₀} {₁} {₄} {₁₄} {()} {jl}
  lemma-[6c] {₀} {₁} {₅} {₁₅} {()} {jl}
  lemma-[6c] {₀} {₁} {₆} {₁₆} {()} {jl}
  lemma-[6c] {₀} {₁} {₇} {₁₇} {()} {jl}
  lemma-[6c] {₀} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₀} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₀} {₂} {₃} {₂₃} {()} {jl}
  lemma-[6c] {₀} {₂} {₄} {₂₄} {()} {jl}
  lemma-[6c] {₀} {₂} {₅} {₂₅} {()} {jl}
  lemma-[6c] {₀} {₂} {₆} {₂₆} {()} {jl}
  lemma-[6c] {₀} {₂} {₇} {₂₇} {()} {jl}
  lemma-[6c] {₀} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₀} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₀} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₀} {₃} {₄} {₃₄} {()} {jl}
  lemma-[6c] {₀} {₃} {₅} {₃₅} {()} {jl}
  lemma-[6c] {₀} {₃} {₆} {₃₆} {()} {jl}
  lemma-[6c] {₀} {₃} {₇} {₃₇} {()} {jl}
  lemma-[6c] {₀} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₀} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₀} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₀} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₀} {₄} {₅} {₄₅} {()} {jl}
  lemma-[6c] {₀} {₄} {₆} {₄₆} {()} {jl}
  lemma-[6c] {₀} {₄} {₇} {₄₇} {()} {jl}
  lemma-[6c] {₀} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₀} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₀} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₀} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₀} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₀} {₅} {₆} {₅₆} {()} {jl}
  lemma-[6c] {₀} {₅} {₇} {₅₇} {()} {jl}
  lemma-[6c] {₀} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₀} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₀} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₀} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₀} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₀} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₀} {₆} {₇} {₆₇} {()} {jl}
  lemma-[6c] {₀} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₀} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₀} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₀} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₀} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₀} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₀} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₀} {₇} {₇} {()} {kj} {jl}
  lemma-[6c] {₁} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₀} {₁} {₀₁} {₀₁} {()}
  lemma-[6c] {₁} {₀} {₂} {₀₂} {₀₁} {₁₂} = by-basis-change (X₀₁) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₁} {₀} {₃} {₀₃} {₀₁} {₁₃} = by-basis-change (X₀₁ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₁} {₀} {₄} {₀₄} {₀₁} {₁₄} = by-basis-change (X₀₁ • X₂₃ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₁} {₀} {₅} {₀₅} {₀₁} {₁₅} = by-basis-change (X₀₁ • X₂₃ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₁} {₀} {₆} {₀₆} {₀₁} {₁₆} = by-basis-change (X₀₁ • X₂₃ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₁} {₀} {₇} {₀₇} {₀₁} {₁₇} = by-basis-change (X₀₁ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₁} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₁} {₁} {₂} {₁₂} {()} {jl}
  lemma-[6c] {₁} {₁} {₃} {₁₃} {()} {jl}
  lemma-[6c] {₁} {₁} {₄} {₁₄} {()} {jl}
  lemma-[6c] {₁} {₁} {₅} {₁₅} {()} {jl}
  lemma-[6c] {₁} {₁} {₆} {₁₆} {()} {jl}
  lemma-[6c] {₁} {₁} {₇} {₁₇} {()} {jl}
  lemma-[6c] {₁} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₁} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₁} {₂} {₃} {₂₃} {()} {jl}
  lemma-[6c] {₁} {₂} {₄} {₂₄} {()} {jl}
  lemma-[6c] {₁} {₂} {₅} {₂₅} {()} {jl}
  lemma-[6c] {₁} {₂} {₆} {₂₆} {()} {jl}
  lemma-[6c] {₁} {₂} {₇} {₂₇} {()} {jl}
  lemma-[6c] {₁} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₁} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₁} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₁} {₃} {₄} {₃₄} {()} {jl}
  lemma-[6c] {₁} {₃} {₅} {₃₅} {()} {jl}
  lemma-[6c] {₁} {₃} {₆} {₃₆} {()} {jl}
  lemma-[6c] {₁} {₃} {₇} {₃₇} {()} {jl}
  lemma-[6c] {₁} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₁} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₁} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₁} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₁} {₄} {₅} {₄₅} {()} {jl}
  lemma-[6c] {₁} {₄} {₆} {₄₆} {()} {jl}
  lemma-[6c] {₁} {₄} {₇} {₄₇} {()} {jl}
  lemma-[6c] {₁} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₁} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₁} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₁} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₁} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₁} {₅} {₆} {₅₆} {()} {jl}
  lemma-[6c] {₁} {₅} {₇} {₅₇} {()} {jl}
  lemma-[6c] {₁} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₁} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₁} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₁} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₁} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₁} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₁} {₆} {₇} {₆₇} {()} {jl}
  lemma-[6c] {₁} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₁} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₁} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₁} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₁} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₁} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₁} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₁} {₇} {₇} {()} {kj} {jl}
  lemma-[6c] {₂} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₀} {₁} {₀₁} {₀₂} {()}
  lemma-[6c] {₂} {₀} {₂} {₀₂} {₀₂} {()}
  lemma-[6c] {₂} {₀} {₃} {₀₃} {₀₂} {₂₃} = by-basis-change (X₀₁ • X₂₃ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₀} {₄} {₀₄} {₀₂} {₂₄} = by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₀} {₅} {₀₅} {₀₂} {₂₅} = by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₀} {₆} {₀₆} {₀₂} {₂₆} = by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₀} {₇} {₀₇} {₀₂} {₂₇} = by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₂} {₁} {₂} {₁₂} {₁₂} {()}
  lemma-[6c] {₂} {₁} {₃} {₁₃} {₁₂} {₂₃} = by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₁} {₄} {₁₄} {₁₂} {₂₄} = by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₁} {₅} {₁₅} {₁₂} {₂₅} = by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₁} {₆} {₁₆} {₁₂} {₂₆} = by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₁} {₇} {₁₇} {₁₂} {₂₇} = by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₂} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₂} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₂} {₂} {₃} {₂₃} {()} {jl}
  lemma-[6c] {₂} {₂} {₄} {₂₄} {()} {jl}
  lemma-[6c] {₂} {₂} {₅} {₂₅} {()} {jl}
  lemma-[6c] {₂} {₂} {₆} {₂₆} {()} {jl}
  lemma-[6c] {₂} {₂} {₇} {₂₇} {()} {jl}
  lemma-[6c] {₂} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₂} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₂} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₂} {₃} {₄} {₃₄} {()} {jl}
  lemma-[6c] {₂} {₃} {₅} {₃₅} {()} {jl}
  lemma-[6c] {₂} {₃} {₆} {₃₆} {()} {jl}
  lemma-[6c] {₂} {₃} {₇} {₃₇} {()} {jl}
  lemma-[6c] {₂} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₂} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₂} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₂} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₂} {₄} {₅} {₄₅} {()} {jl}
  lemma-[6c] {₂} {₄} {₆} {₄₆} {()} {jl}
  lemma-[6c] {₂} {₄} {₇} {₄₇} {()} {jl}
  lemma-[6c] {₂} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₂} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₂} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₂} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₂} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₂} {₅} {₆} {₅₆} {()} {jl}
  lemma-[6c] {₂} {₅} {₇} {₅₇} {()} {jl}
  lemma-[6c] {₂} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₂} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₂} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₂} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₂} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₂} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₂} {₆} {₇} {₆₇} {()} {jl}
  lemma-[6c] {₂} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₂} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₂} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₂} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₂} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₂} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₂} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₂} {₇} {₇} {()} {kj} {jl}
  lemma-[6c] {₃} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₀} {₁} {₀₁} {₀₃} {()}
  lemma-[6c] {₃} {₀} {₂} {₀₂} {₀₃} {()}
  lemma-[6c] {₃} {₀} {₃} {₀₃} {₀₃} {()}
  lemma-[6c] {₃} {₀} {₄} {₀₄} {₀₃} {₃₄} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₀} {₅} {₀₅} {₀₃} {₃₅} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₀} {₆} {₀₆} {₀₃} {₃₆} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₀} {₇} {₀₇} {₀₃} {₃₇} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₃} {₁} {₂} {₁₂} {₁₃} {()}
  lemma-[6c] {₃} {₁} {₃} {₁₃} {₁₃} {()}
  lemma-[6c] {₃} {₁} {₄} {₁₄} {₁₃} {₃₄} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₁} {₅} {₁₅} {₁₃} {₃₅} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₁} {₆} {₁₆} {₁₃} {₃₆} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₁} {₇} {₁₇} {₁₃} {₃₇} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₃} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₃} {₂} {₃} {₂₃} {₂₃} {()}
  lemma-[6c] {₃} {₂} {₄} {₂₄} {₂₃} {₃₄} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₂} {₅} {₂₅} {₂₃} {₃₅} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃ • X₄₅) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₂} {₆} {₂₆} {₂₃} {₃₆} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃ • X₄₅ • X₅₆) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₂} {₇} {₂₇} {₂₃} {₃₇} = by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃ • X₄₅ • X₅₆ • X₆₇) ((lemma-i₀-K₁₂=K₁₂-i₀)) 200 auto
  lemma-[6c] {₃} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₃} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₃} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₃} {₃} {₄} {₃₄} {()} {jl}
  lemma-[6c] {₃} {₃} {₅} {₃₅} {()} {jl}
  lemma-[6c] {₃} {₃} {₆} {₃₆} {()} {jl}
  lemma-[6c] {₃} {₃} {₇} {₃₇} {()} {jl}
  lemma-[6c] {₃} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₃} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₃} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₃} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₃} {₄} {₅} {₄₅} {()} {jl}
  lemma-[6c] {₃} {₄} {₆} {₄₆} {()} {jl}
  lemma-[6c] {₃} {₄} {₇} {₄₇} {()} {jl}
  lemma-[6c] {₃} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₃} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₃} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₃} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₃} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₃} {₅} {₆} {₅₆} {()} {jl}
  lemma-[6c] {₃} {₅} {₇} {₅₇} {()} {jl}
  lemma-[6c] {₃} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₃} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₃} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₃} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₃} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₃} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₃} {₆} {₇} {₆₇} {()} {jl}
  lemma-[6c] {₃} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₃} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₃} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₃} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₃} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₃} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₃} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₃} {₇} {₇} {()} {kj} {jl}
  lemma-[6c] {₄} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₀} {₁} {₀₁} {₀₄} {()}
  lemma-[6c] {₄} {₀} {₂} {₀₂} {₀₄} {()}
  lemma-[6c] {₄} {₀} {₃} {₀₃} {₀₄} {()}
  lemma-[6c] {₄} {₀} {₄} {₀₄} {₀₄} {()}
  lemma-[6c] {₄} {₀} {₅} {₀₅} {₀₄} {₄₅} = by-basis-change (X₀₄) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₀} {₆} {₀₆} {₀₄} {₄₆} = by-basis-change (X₀₄ • X₅₆) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₀} {₇} {₀₇} {₀₄} {₄₇} = by-basis-change (X₀₄ • X₅₆ • X₆₇) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₄} {₁} {₂} {₁₂} {₁₄} {()}
  lemma-[6c] {₄} {₁} {₃} {₁₃} {₁₄} {()}
  lemma-[6c] {₄} {₁} {₄} {₁₄} {₁₄} {()}
  lemma-[6c] {₄} {₁} {₅} {₁₅} {₁₄} {₄₅} = by-basis-change (X₀₄ • X₀₁) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₁} {₆} {₁₆} {₁₄} {₄₆} = by-basis-change (X₀₄ • X₀₁ • X₅₆) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₁} {₇} {₁₇} {₁₄} {₄₇} = by-basis-change (X₀₄ • X₀₁ • X₅₆ • X₆₇) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₄} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₄} {₂} {₃} {₂₃} {₂₄} {()}
  lemma-[6c] {₄} {₂} {₄} {₂₄} {₂₄} {()}
  lemma-[6c] {₄} {₂} {₅} {₂₅} {₂₄} {₄₅} = by-basis-change (X₀₄ • X₀₁ • X₁₂) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₂} {₆} {₂₆} {₂₄} {₄₆} = by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₅₆) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₂} {₇} {₂₇} {₂₄} {₄₇} = by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₅₆ • X₆₇) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₄} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₄} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₄} {₃} {₄} {₃₄} {₃₄} {()}
  lemma-[6c] {₄} {₃} {₅} {₃₅} {₃₄} {₄₅} = by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₂₃) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₃} {₆} {₃₆} {₃₄} {₄₆} = by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₂₃ • X₅₆) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₃} {₇} {₃₇} {₃₄} {₄₇} = by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₂₃ • X₅₆ • X₆₇) ((lemma-[S6d])) 200 auto
  lemma-[6c] {₄} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₄} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₄} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₄} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₄} {₄} {₅} {₄₅} {()} {jl}
  lemma-[6c] {₄} {₄} {₆} {₄₆} {()} {jl}
  lemma-[6c] {₄} {₄} {₇} {₄₇} {()} {jl}
  lemma-[6c] {₄} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₄} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₄} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₄} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₄} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₄} {₅} {₆} {₅₆} {()} {jl}
  lemma-[6c] {₄} {₅} {₇} {₅₇} {()} {jl}
  lemma-[6c] {₄} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₄} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₄} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₄} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₄} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₄} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₄} {₆} {₇} {₆₇} {()} {jl}
  lemma-[6c] {₄} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₄} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₄} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₄} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₄} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₄} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₄} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₄} {₇} {₇} {()} {kj} {jl}
  lemma-[6c] {₅} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₀} {₁} {₀₁} {₀₅} {()}
  lemma-[6c] {₅} {₀} {₂} {₀₂} {₀₅} {()}
  lemma-[6c] {₅} {₀} {₃} {₀₃} {₀₅} {()}
  lemma-[6c] {₅} {₀} {₄} {₀₄} {₀₅} {()}
  lemma-[6c] {₅} {₀} {₅} {₀₅} {₀₅} {()}
  lemma-[6c] {₅} {₀} {₆} {₀₆} {₀₅} {₅₆} = by-basis-change (X₀₅) ((lemma-[S6e])) 200 auto
  lemma-[6c] {₅} {₀} {₇} {₀₇} {₀₅} {₅₇} = by-basis-change (X₀₅ • X₆₇) ((lemma-[S6e])) 400 auto
  lemma-[6c] {₅} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₅} {₁} {₂} {₁₂} {₁₅} {()}
  lemma-[6c] {₅} {₁} {₃} {₁₃} {₁₅} {()}
  lemma-[6c] {₅} {₁} {₄} {₁₄} {₁₅} {()}
  lemma-[6c] {₅} {₁} {₅} {₁₅} {₁₅} {()}
  lemma-[6c] {₅} {₁} {₆} {₁₆} {₁₅} {₅₆} = by-basis-change (X₀₅ • X₀₁) ((lemma-[S6e])) 200 auto
  lemma-[6c] {₅} {₁} {₇} {₁₇} {₁₅} {₅₇} = by-basis-change (X₀₅ • X₀₁ • X₆₇) ((lemma-[S6e])) 400 auto
  lemma-[6c] {₅} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₅} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₅} {₂} {₃} {₂₃} {₂₅} {()}
  lemma-[6c] {₅} {₂} {₄} {₂₄} {₂₅} {()}
  lemma-[6c] {₅} {₂} {₅} {₂₅} {₂₅} {()}
  lemma-[6c] {₅} {₂} {₆} {₂₆} {₂₅} {₅₆} = by-basis-change (X₀₅ • X₀₁ • X₁₂) ((lemma-[S6e])) 200 auto
  lemma-[6c] {₅} {₂} {₇} {₂₇} {₂₅} {₅₇} = by-basis-change (X₀₅ • X₀₁ • X₁₂ • X₆₇) ((lemma-[S6e])) 400 auto
  lemma-[6c] {₅} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₅} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₅} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₅} {₃} {₄} {₃₄} {₃₅} {()}
  lemma-[6c] {₅} {₃} {₅} {₃₅} {₃₅} {()}
  lemma-[6c] {₅} {₃} {₆} {₃₆} {₃₅} {₅₆} = by-basis-change (X₀₅ • X₀₁ • X₁₂ • X₂₃) ((lemma-[S6e])) 200 auto
  lemma-[6c] {₅} {₃} {₇} {₃₇} {₃₅} {₅₇} = by-basis-change (X₀₅ • X₀₁ • X₁₂ • X₂₃ • X₆₇) ((lemma-[S6e])) 400 auto
  lemma-[6c] {₅} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₅} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₅} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₅} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₅} {₄} {₅} {₄₅} {₄₅} {()}
  lemma-[6c] {₅} {₄} {₆} {₄₆} {₄₅} {₅₆} = by-basis-change (X₀₄ • X₄₅) ((lemma-[S6e])) 200 auto
  lemma-[6c] {₅} {₄} {₇} {₄₇} {₄₅} {₅₇} = by-basis-change (X₀₄ • X₄₅ • X₆₇) ((lemma-[S6e])) 400 auto
  lemma-[6c] {₅} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₅} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₅} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₅} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₅} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₅} {₅} {₆} {₅₆} {()} {jl}
  lemma-[6c] {₅} {₅} {₇} {₅₇} {()} {jl}
  lemma-[6c] {₅} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₅} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₅} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₅} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₅} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₅} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₅} {₆} {₇} {₆₇} {()} {jl}
  lemma-[6c] {₅} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₅} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₅} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₅} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₅} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₅} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₅} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₅} {₇} {₇} {()} {kj} {jl}
  lemma-[6c] {₆} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₀} {₁} {₀₁} {₀₆} {()}
  lemma-[6c] {₆} {₀} {₂} {₀₂} {₀₆} {()}
  lemma-[6c] {₆} {₀} {₃} {₀₃} {₀₆} {()}
  lemma-[6c] {₆} {₀} {₄} {₀₄} {₀₆} {()}
  lemma-[6c] {₆} {₀} {₅} {₀₅} {₀₆} {()}
  lemma-[6c] {₆} {₀} {₆} {₀₆} {₀₆} {()}
  lemma-[6c] {₆} {₀} {₇} {₀₇} {₀₆} {₆₇} = by-basis-change (X₀₆) ((lemma-[S6f])) 200 auto
  lemma-[6c] {₆} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₆} {₁} {₂} {₁₂} {₁₆} {()}
  lemma-[6c] {₆} {₁} {₃} {₁₃} {₁₆} {()}
  lemma-[6c] {₆} {₁} {₄} {₁₄} {₁₆} {()}
  lemma-[6c] {₆} {₁} {₅} {₁₅} {₁₆} {()}
  lemma-[6c] {₆} {₁} {₆} {₁₆} {₁₆} {()}
  lemma-[6c] {₆} {₁} {₇} {₁₇} {₁₆} {₆₇} = by-basis-change (X₀₆ • X₀₁) ((lemma-[S6f])) 200 auto
  lemma-[6c] {₆} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₆} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₆} {₂} {₃} {₂₃} {₂₆} {()}
  lemma-[6c] {₆} {₂} {₄} {₂₄} {₂₆} {()}
  lemma-[6c] {₆} {₂} {₅} {₂₅} {₂₆} {()}
  lemma-[6c] {₆} {₂} {₆} {₂₆} {₂₆} {()}
  lemma-[6c] {₆} {₂} {₇} {₂₇} {₂₆} {₆₇} = by-basis-change (X₀₆ • X₀₁ • X₁₂) ((lemma-[S6f])) 200 auto
  lemma-[6c] {₆} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₆} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₆} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₆} {₃} {₄} {₃₄} {₃₆} {()}
  lemma-[6c] {₆} {₃} {₅} {₃₅} {₃₆} {()}
  lemma-[6c] {₆} {₃} {₆} {₃₆} {₃₆} {()}
  lemma-[6c] {₆} {₃} {₇} {₃₇} {₃₆} {₆₇} = by-basis-change (X₀₆ • X₀₁ • X₁₂ • X₂₃) ((lemma-[S6f])) 200 auto
  lemma-[6c] {₆} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₆} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₆} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₆} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₆} {₄} {₅} {₄₅} {₄₆} {()}
  lemma-[6c] {₆} {₄} {₆} {₄₆} {₄₆} {()}
  lemma-[6c] {₆} {₄} {₇} {₄₇} {₄₆} {₆₇} = by-basis-change (X₀₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄) ((lemma-[S6f])) 200 auto
  lemma-[6c] {₆} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₆} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₆} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₆} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₆} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₆} {₅} {₆} {₅₆} {₅₆} {()}
  lemma-[6c] {₆} {₅} {₇} {₅₇} {₅₆} {₆₇} = by-basis-change (X₀₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((lemma-[S6f])) 200 auto
  lemma-[6c] {₆} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₆} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₆} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₆} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₆} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₆} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₆} {₆} {₇} {₆₇} {()} {jl}
  lemma-[6c] {₆} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₆} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₆} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₆} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₆} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₆} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₆} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₆} {₇} {₇} {()} {kj} {jl}
  lemma-[6c] {₇} {₀} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₀} {₁} {₀₁} {₀₇} {()}
  lemma-[6c] {₇} {₀} {₂} {₀₂} {₀₇} {()}
  lemma-[6c] {₇} {₀} {₃} {₀₃} {₀₇} {()}
  lemma-[6c] {₇} {₀} {₄} {₀₄} {₀₇} {()}
  lemma-[6c] {₇} {₀} {₅} {₀₅} {₀₇} {()}
  lemma-[6c] {₇} {₀} {₆} {₀₆} {₀₇} {()}
  lemma-[6c] {₇} {₀} {₇} {₀₇} {₀₇} {()}
  lemma-[6c] {₇} {₁} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₁} {₁} {()} {kj} {jl}
  lemma-[6c] {₇} {₁} {₂} {₁₂} {₁₇} {()}
  lemma-[6c] {₇} {₁} {₃} {₁₃} {₁₇} {()}
  lemma-[6c] {₇} {₁} {₄} {₁₄} {₁₇} {()}
  lemma-[6c] {₇} {₁} {₅} {₁₅} {₁₇} {()}
  lemma-[6c] {₇} {₁} {₆} {₁₆} {₁₇} {()}
  lemma-[6c] {₇} {₁} {₇} {₁₇} {₁₇} {()}
  lemma-[6c] {₇} {₂} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₂} {₁} {()} {kj} {jl}
  lemma-[6c] {₇} {₂} {₂} {()} {kj} {jl}
  lemma-[6c] {₇} {₂} {₃} {₂₃} {₂₇} {()}
  lemma-[6c] {₇} {₂} {₄} {₂₄} {₂₇} {()}
  lemma-[6c] {₇} {₂} {₅} {₂₅} {₂₇} {()}
  lemma-[6c] {₇} {₂} {₆} {₂₆} {₂₇} {()}
  lemma-[6c] {₇} {₂} {₇} {₂₇} {₂₇} {()}
  lemma-[6c] {₇} {₃} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₃} {₁} {()} {kj} {jl}
  lemma-[6c] {₇} {₃} {₂} {()} {kj} {jl}
  lemma-[6c] {₇} {₃} {₃} {()} {kj} {jl}
  lemma-[6c] {₇} {₃} {₄} {₃₄} {₃₇} {()}
  lemma-[6c] {₇} {₃} {₅} {₃₅} {₃₇} {()}
  lemma-[6c] {₇} {₃} {₆} {₃₆} {₃₇} {()}
  lemma-[6c] {₇} {₃} {₇} {₃₇} {₃₇} {()}
  lemma-[6c] {₇} {₄} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₄} {₁} {()} {kj} {jl}
  lemma-[6c] {₇} {₄} {₂} {()} {kj} {jl}
  lemma-[6c] {₇} {₄} {₃} {()} {kj} {jl}
  lemma-[6c] {₇} {₄} {₄} {()} {kj} {jl}
  lemma-[6c] {₇} {₄} {₅} {₄₅} {₄₇} {()}
  lemma-[6c] {₇} {₄} {₆} {₄₆} {₄₇} {()}
  lemma-[6c] {₇} {₄} {₇} {₄₇} {₄₇} {()}
  lemma-[6c] {₇} {₅} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₅} {₁} {()} {kj} {jl}
  lemma-[6c] {₇} {₅} {₂} {()} {kj} {jl}
  lemma-[6c] {₇} {₅} {₃} {()} {kj} {jl}
  lemma-[6c] {₇} {₅} {₄} {()} {kj} {jl}
  lemma-[6c] {₇} {₅} {₅} {()} {kj} {jl}
  lemma-[6c] {₇} {₅} {₆} {₅₆} {₅₇} {()}
  lemma-[6c] {₇} {₅} {₇} {₅₇} {₅₇} {()}
  lemma-[6c] {₇} {₆} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₆} {₁} {()} {kj} {jl}
  lemma-[6c] {₇} {₆} {₂} {()} {kj} {jl}
  lemma-[6c] {₇} {₆} {₃} {()} {kj} {jl}
  lemma-[6c] {₇} {₆} {₄} {()} {kj} {jl}
  lemma-[6c] {₇} {₆} {₅} {()} {kj} {jl}
  lemma-[6c] {₇} {₆} {₆} {()} {kj} {jl}
  lemma-[6c] {₇} {₆} {₇} {₆₇} {₆₇} {()}
  lemma-[6c] {₇} {₇} {₀} {()} {kj} {jl}
  lemma-[6c] {₇} {₇} {₁} {()} {kj} {jl}
  lemma-[6c] {₇} {₇} {₂} {()} {kj} {jl}
  lemma-[6c] {₇} {₇} {₃} {()} {kj} {jl}
  lemma-[6c] {₇} {₇} {₄} {()} {kj} {jl}
  lemma-[6c] {₇} {₇} {₅} {()} {kj} {jl}
  lemma-[6c] {₇} {₇} {₆} {()} {kj} {jl}
  lemma-[6c] {₇} {₇} {₇} {()} {kj} {jl}

