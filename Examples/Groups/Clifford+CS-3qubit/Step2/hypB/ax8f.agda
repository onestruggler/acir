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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8f where

  lemma-[S7a]' : TwoLevel-Simplified.Rel ⊢ X₀₁ • K₂₃ === K₂₃ • X₀₁
  lemma-[S7a]' = by-basis-change (X₀₂ • X₁₃) (axiom [S7a]) 100 auto

  lemma-[S7a]'' : TwoLevel-Simplified.Rel ⊢ X₂₃ • K₀₁ === K₀₁ • X₂₃
  lemma-[S7a]'' = symm (axiom [S7a])


  lemma-[S8f]' : TwoLevel-Simplified.Rel ⊢ X₁₂ • K₃₄ === K₃₄ • X₁₂
  lemma-[S8f]' = by-basis-change (X₃₄ • X₁₄ • X₀₃) (axiom [S7a]) 100 auto


  lemma-[S8f]'' : TwoLevel-Simplified.Rel ⊢ X₃₄ • K₁₂ === K₁₂ • X₃₄
  lemma-[S8f]'' = by-basis-change (X₁₃ • X₂₄) (lemma-[S8f]') 100 auto

  lemma-[S8j]' : TwoLevel-Simplified.Rel ⊢ X₂₃ • K₄₅ === K₄₅ • X₂₃
  lemma-[S8j]' = by-basis-change (X₁₅ • X₀₄) (axiom [S7a]) 100 auto

  lemma-[S8j]'' : TwoLevel-Simplified.Rel ⊢ X₄₅ • K₂₃ === K₂₃ • X₄₅
  lemma-[S8j]'' = by-basis-change (X₃₅ • X₂₄) (lemma-[S8j]') 100 auto

  lemma-[S8m]' : TwoLevel-Simplified.Rel ⊢ X₃₄ • K₅₆ === K₅₆ • X₃₄
  lemma-[S8m]' = by-basis-change (X₂₄ • X₁₆ • X₀₅) (axiom [S7a]) 100 auto

  lemma-[S8m]'' : TwoLevel-Simplified.Rel ⊢  X₅₆ • K₃₄ === K₃₄ • X₅₆
  lemma-[S8m]'' = by-basis-change (X₄₆ • X₃₅) (lemma-[S8m]') 100 auto


  lemma-[8b'] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Less j l} -> {mk : Less m k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (X lm • K jk) === (g ʷ) (K jk • X lm)
  lemma-[8b'] {jk = ₀₁} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₀₁} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₀₁} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₀₁} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₀₁} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₀₁} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₀₁} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₀₁} {₁₂} {₀₁} {()}
  lemma-[8b'] {jk = ₀₁} {₁₃} {₀₁} {()}
  lemma-[8b'] {jk = ₀₁} {₁₄} {₀₁} {()}
  lemma-[8b'] {jk = ₀₁} {₁₅} {₀₁} {()}
  lemma-[8b'] {jk = ₀₁} {₁₆} {₀₁} {()}
  lemma-[8b'] {jk = ₀₁} {₁₇} {₀₁} {()}
  lemma-[8b'] {jk = ₀₁} {₂₃} {₀₂} {()}
  lemma-[8b'] {jk = ₀₁} {₂₄} {₀₂} {()}
  lemma-[8b'] {jk = ₀₁} {₂₅} {₀₂} {()}
  lemma-[8b'] {jk = ₀₁} {₂₆} {₀₂} {()}
  lemma-[8b'] {jk = ₀₁} {₂₇} {₀₂} {()}
  lemma-[8b'] {jk = ₀₁} {₃₄} {₀₃} {()}
  lemma-[8b'] {jk = ₀₁} {₃₅} {₀₃} {()}
  lemma-[8b'] {jk = ₀₁} {₃₆} {₀₃} {()}
  lemma-[8b'] {jk = ₀₁} {₃₇} {₀₃} {()}
  lemma-[8b'] {jk = ₀₁} {₄₅} {₀₄} {()}
  lemma-[8b'] {jk = ₀₁} {₄₆} {₀₄} {()}
  lemma-[8b'] {jk = ₀₁} {₄₇} {₀₄} {()}
  lemma-[8b'] {jk = ₀₁} {₅₆} {₀₅} {()}
  lemma-[8b'] {jk = ₀₁} {₅₇} {₀₅} {()}
  lemma-[8b'] {jk = ₀₁} {₆₇} {₀₆} {()}
  lemma-[8b'] {jk = ₀₂} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₀₂} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₀₂} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₀₂} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₀₂} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₀₂} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₀₂} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₀₂} {₁₂} {₀₁} {()}
  lemma-[8b'] {jk = ₀₂} {₁₃} {₀₁} {()}
  lemma-[8b'] {jk = ₀₂} {₁₄} {₀₁} {()}
  lemma-[8b'] {jk = ₀₂} {₁₅} {₀₁} {()}
  lemma-[8b'] {jk = ₀₂} {₁₆} {₀₁} {()}
  lemma-[8b'] {jk = ₀₂} {₁₇} {₀₁} {()}
  lemma-[8b'] {jk = ₀₂} {₂₃} {₀₂} {()}
  lemma-[8b'] {jk = ₀₂} {₂₄} {₀₂} {()}
  lemma-[8b'] {jk = ₀₂} {₂₅} {₀₂} {()}
  lemma-[8b'] {jk = ₀₂} {₂₆} {₀₂} {()}
  lemma-[8b'] {jk = ₀₂} {₂₇} {₀₂} {()}
  lemma-[8b'] {jk = ₀₂} {₃₄} {₀₃} {()}
  lemma-[8b'] {jk = ₀₂} {₃₅} {₀₃} {()}
  lemma-[8b'] {jk = ₀₂} {₃₆} {₀₃} {()}
  lemma-[8b'] {jk = ₀₂} {₃₇} {₀₃} {()}
  lemma-[8b'] {jk = ₀₂} {₄₅} {₀₄} {()}
  lemma-[8b'] {jk = ₀₂} {₄₆} {₀₄} {()}
  lemma-[8b'] {jk = ₀₂} {₄₇} {₀₄} {()}
  lemma-[8b'] {jk = ₀₂} {₅₆} {₀₅} {()}
  lemma-[8b'] {jk = ₀₂} {₅₇} {₀₅} {()}
  lemma-[8b'] {jk = ₀₂} {₆₇} {₀₆} {()}
  lemma-[8b'] {jk = ₀₃} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₀₃} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₀₃} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₀₃} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₀₃} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₀₃} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₀₃} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₀₃} {₁₂} {₀₁} {₂₃} = by-basis-change (X₀₁ • X₀₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₃} {₁₃} {₀₁} {()}
  lemma-[8b'] {jk = ₀₃} {₁₄} {₀₁} {()}
  lemma-[8b'] {jk = ₀₃} {₁₅} {₀₁} {()}
  lemma-[8b'] {jk = ₀₃} {₁₆} {₀₁} {()}
  lemma-[8b'] {jk = ₀₃} {₁₇} {₀₁} {()}
  lemma-[8b'] {jk = ₀₃} {₂₃} {₀₂} {()}
  lemma-[8b'] {jk = ₀₃} {₂₄} {₀₂} {()}
  lemma-[8b'] {jk = ₀₃} {₂₅} {₀₂} {()}
  lemma-[8b'] {jk = ₀₃} {₂₆} {₀₂} {()}
  lemma-[8b'] {jk = ₀₃} {₂₇} {₀₂} {()}
  lemma-[8b'] {jk = ₀₃} {₃₄} {₀₃} {()}
  lemma-[8b'] {jk = ₀₃} {₃₅} {₀₃} {()}
  lemma-[8b'] {jk = ₀₃} {₃₆} {₀₃} {()}
  lemma-[8b'] {jk = ₀₃} {₃₇} {₀₃} {()}
  lemma-[8b'] {jk = ₀₃} {₄₅} {₀₄} {()}
  lemma-[8b'] {jk = ₀₃} {₄₆} {₀₄} {()}
  lemma-[8b'] {jk = ₀₃} {₄₇} {₀₄} {()}
  lemma-[8b'] {jk = ₀₃} {₅₆} {₀₅} {()}
  lemma-[8b'] {jk = ₀₃} {₅₇} {₀₅} {()}
  lemma-[8b'] {jk = ₀₃} {₆₇} {₀₆} {()}
  lemma-[8b'] {jk = ₀₄} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₀₄} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₀₄} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₀₄} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₀₄} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₀₄} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₀₄} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₀₄} {₁₂} {₀₁} {₂₄} = by-basis-change (X₀₁ • X₀₂ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₄} {₁₃} {₀₁} {₃₄} = by-basis-change (X₀₁ • X₀₂ • X₃₄ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₄} {₁₄} {₀₁} {()}
  lemma-[8b'] {jk = ₀₄} {₁₅} {₀₁} {()}
  lemma-[8b'] {jk = ₀₄} {₁₆} {₀₁} {()}
  lemma-[8b'] {jk = ₀₄} {₁₇} {₀₁} {()}
  lemma-[8b'] {jk = ₀₄} {₂₃} {₀₂} {₃₄} = by-basis-change (X₀₁ • X₀₂ • X₃₄ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₄} {₂₄} {₀₂} {()}
  lemma-[8b'] {jk = ₀₄} {₂₅} {₀₂} {()}
  lemma-[8b'] {jk = ₀₄} {₂₆} {₀₂} {()}
  lemma-[8b'] {jk = ₀₄} {₂₇} {₀₂} {()}
  lemma-[8b'] {jk = ₀₄} {₃₄} {₀₃} {()}
  lemma-[8b'] {jk = ₀₄} {₃₅} {₀₃} {()}
  lemma-[8b'] {jk = ₀₄} {₃₆} {₀₃} {()}
  lemma-[8b'] {jk = ₀₄} {₃₇} {₀₃} {()}
  lemma-[8b'] {jk = ₀₄} {₄₅} {₀₄} {()}
  lemma-[8b'] {jk = ₀₄} {₄₆} {₀₄} {()}
  lemma-[8b'] {jk = ₀₄} {₄₇} {₀₄} {()}
  lemma-[8b'] {jk = ₀₄} {₅₆} {₀₅} {()}
  lemma-[8b'] {jk = ₀₄} {₅₇} {₀₅} {()}
  lemma-[8b'] {jk = ₀₄} {₆₇} {₀₆} {()}
  lemma-[8b'] {jk = ₀₅} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₀₅} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₀₅} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₀₅} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₀₅} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₀₅} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₀₅} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₀₅} {₁₂} {₀₁} {₂₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₅} {₁₃} {₀₁} {₃₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₅} {₁₄} {₀₁} {₄₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₅} {₁₅} {₀₁} {()}
  lemma-[8b'] {jk = ₀₅} {₁₆} {₀₁} {()}
  lemma-[8b'] {jk = ₀₅} {₁₇} {₀₁} {()}
  lemma-[8b'] {jk = ₀₅} {₂₃} {₀₂} {₃₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₅} {₂₄} {₀₂} {₄₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₄ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₅} {₂₅} {₀₂} {()}
  lemma-[8b'] {jk = ₀₅} {₂₆} {₀₂} {()}
  lemma-[8b'] {jk = ₀₅} {₂₇} {₀₂} {()}
  lemma-[8b'] {jk = ₀₅} {₃₄} {₀₃} {₄₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₄ • X₁₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₅} {₃₅} {₀₃} {()}
  lemma-[8b'] {jk = ₀₅} {₃₆} {₀₃} {()}
  lemma-[8b'] {jk = ₀₅} {₃₇} {₀₃} {()}
  lemma-[8b'] {jk = ₀₅} {₄₅} {₀₄} {()}
  lemma-[8b'] {jk = ₀₅} {₄₆} {₀₄} {()}
  lemma-[8b'] {jk = ₀₅} {₄₇} {₀₄} {()}
  lemma-[8b'] {jk = ₀₅} {₅₆} {₀₅} {()}
  lemma-[8b'] {jk = ₀₅} {₅₇} {₀₅} {()}
  lemma-[8b'] {jk = ₀₅} {₆₇} {₀₆} {()}
  lemma-[8b'] {jk = ₀₆} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₀₆} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₀₆} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₀₆} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₀₆} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₀₆} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₀₆} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₀₆} {₁₂} {₀₁} {₂₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₁₃} {₀₁} {₃₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₁₄} {₀₁} {₄₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₁₅} {₀₁} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₁₆} {₀₁} {()}
  lemma-[8b'] {jk = ₀₆} {₁₇} {₀₁} {()}
  lemma-[8b'] {jk = ₀₆} {₂₃} {₀₂} {₃₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₂₄} {₀₂} {₄₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₄ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₂₅} {₀₂} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₂₆} {₀₂} {()}
  lemma-[8b'] {jk = ₀₆} {₂₇} {₀₂} {()}
  lemma-[8b'] {jk = ₀₆} {₃₄} {₀₃} {₄₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₃₅} {₀₃} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₃₆} {₀₃} {()}
  lemma-[8b'] {jk = ₀₆} {₃₇} {₀₃} {()}
  lemma-[8b'] {jk = ₀₆} {₄₅} {₀₄} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₆} {₄₆} {₀₄} {()}
  lemma-[8b'] {jk = ₀₆} {₄₇} {₀₄} {()}
  lemma-[8b'] {jk = ₀₆} {₅₆} {₀₅} {()}
  lemma-[8b'] {jk = ₀₆} {₅₇} {₀₅} {()}
  lemma-[8b'] {jk = ₀₆} {₆₇} {₀₆} {()}
  lemma-[8b'] {jk = ₀₇} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₀₇} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₀₇} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₀₇} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₀₇} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₀₇} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₀₇} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₀₇} {₁₂} {₀₁} {₂₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₁₃} {₀₁} {₃₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₁₄} {₀₁} {₄₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₄) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₁₅} {₀₁} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₁₆} {₀₁} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₁₇} {₀₁} {()}
  lemma-[8b'] {jk = ₀₇} {₂₃} {₀₂} {₃₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₃ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₂₄} {₀₂} {₄₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₄ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₂₅} {₀₂} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₂₆} {₀₂} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₂₇} {₀₂} {()}
  lemma-[8b'] {jk = ₀₇} {₃₄} {₀₃} {₄₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₃₅} {₀₃} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₃₆} {₀₃} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₃₇} {₀₃} {()}
  lemma-[8b'] {jk = ₀₇} {₄₅} {₀₄} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₄₆} {₀₄} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₄₇} {₀₄} {()}
  lemma-[8b'] {jk = ₀₇} {₅₆} {₀₅} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (lemma-[S7a]') 100 auto
  lemma-[8b'] {jk = ₀₇} {₅₇} {₀₅} {()}
  lemma-[8b'] {jk = ₀₇} {₆₇} {₀₆} {()}
  lemma-[8b'] {jk = ₁₂} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₁₂} {₂₃} {₁₂} {()}
  lemma-[8b'] {jk = ₁₂} {₂₄} {₁₂} {()}
  lemma-[8b'] {jk = ₁₂} {₂₅} {₁₂} {()}
  lemma-[8b'] {jk = ₁₂} {₂₆} {₁₂} {()}
  lemma-[8b'] {jk = ₁₂} {₂₇} {₁₂} {()}
  lemma-[8b'] {jk = ₁₂} {₃₄} {₁₃} {()}
  lemma-[8b'] {jk = ₁₂} {₃₅} {₁₃} {()}
  lemma-[8b'] {jk = ₁₂} {₃₆} {₁₃} {()}
  lemma-[8b'] {jk = ₁₂} {₃₇} {₁₃} {()}
  lemma-[8b'] {jk = ₁₂} {₄₅} {₁₄} {()}
  lemma-[8b'] {jk = ₁₂} {₄₆} {₁₄} {()}
  lemma-[8b'] {jk = ₁₂} {₄₇} {₁₄} {()}
  lemma-[8b'] {jk = ₁₂} {₅₆} {₁₅} {()}
  lemma-[8b'] {jk = ₁₂} {₅₇} {₁₅} {()}
  lemma-[8b'] {jk = ₁₂} {₆₇} {₁₆} {()}
  lemma-[8b'] {jk = ₁₃} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₁₃} {₂₃} {₁₂} {()}
  lemma-[8b'] {jk = ₁₃} {₂₄} {₁₂} {()}
  lemma-[8b'] {jk = ₁₃} {₂₅} {₁₂} {()}
  lemma-[8b'] {jk = ₁₃} {₂₆} {₁₂} {()}
  lemma-[8b'] {jk = ₁₃} {₂₇} {₁₂} {()}
  lemma-[8b'] {jk = ₁₃} {₃₄} {₁₃} {()}
  lemma-[8b'] {jk = ₁₃} {₃₅} {₁₃} {()}
  lemma-[8b'] {jk = ₁₃} {₃₆} {₁₃} {()}
  lemma-[8b'] {jk = ₁₃} {₃₇} {₁₃} {()}
  lemma-[8b'] {jk = ₁₃} {₄₅} {₁₄} {()}
  lemma-[8b'] {jk = ₁₃} {₄₆} {₁₄} {()}
  lemma-[8b'] {jk = ₁₃} {₄₇} {₁₄} {()}
  lemma-[8b'] {jk = ₁₃} {₅₆} {₁₅} {()}
  lemma-[8b'] {jk = ₁₃} {₅₇} {₁₅} {()}
  lemma-[8b'] {jk = ₁₃} {₆₇} {₁₆} {()}
  lemma-[8b'] {jk = ₁₄} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₁₄} {₂₃} {₁₂} {₃₄} = by-basis-change (X₀₁ • X₀₄) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₄} {₂₄} {₁₂} {()}
  lemma-[8b'] {jk = ₁₄} {₂₅} {₁₂} {()}
  lemma-[8b'] {jk = ₁₄} {₂₆} {₁₂} {()}
  lemma-[8b'] {jk = ₁₄} {₂₇} {₁₂} {()}
  lemma-[8b'] {jk = ₁₄} {₃₄} {₁₃} {()}
  lemma-[8b'] {jk = ₁₄} {₃₅} {₁₃} {()}
  lemma-[8b'] {jk = ₁₄} {₃₆} {₁₃} {()}
  lemma-[8b'] {jk = ₁₄} {₃₇} {₁₃} {()}
  lemma-[8b'] {jk = ₁₄} {₄₅} {₁₄} {()}
  lemma-[8b'] {jk = ₁₄} {₄₆} {₁₄} {()}
  lemma-[8b'] {jk = ₁₄} {₄₇} {₁₄} {()}
  lemma-[8b'] {jk = ₁₄} {₅₆} {₁₅} {()}
  lemma-[8b'] {jk = ₁₄} {₅₇} {₁₅} {()}
  lemma-[8b'] {jk = ₁₄} {₆₇} {₁₆} {()}
  lemma-[8b'] {jk = ₁₅} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₁₅} {₂₃} {₁₂} {₃₅} = by-basis-change (X₀₁ • X₀₅) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₅} {₂₄} {₁₂} {₄₅} = by-basis-change (X₀₁ • X₀₅ • X₃₄) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₅} {₂₅} {₁₂} {()}
  lemma-[8b'] {jk = ₁₅} {₂₆} {₁₂} {()}
  lemma-[8b'] {jk = ₁₅} {₂₇} {₁₂} {()}
  lemma-[8b'] {jk = ₁₅} {₃₄} {₁₃} {₄₅} = by-basis-change (X₀₁ • X₀₅ • X₃₄ • X₂₃) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₅} {₃₅} {₁₃} {()}
  lemma-[8b'] {jk = ₁₅} {₃₆} {₁₃} {()}
  lemma-[8b'] {jk = ₁₅} {₃₇} {₁₃} {()}
  lemma-[8b'] {jk = ₁₅} {₄₅} {₁₄} {()}
  lemma-[8b'] {jk = ₁₅} {₄₆} {₁₄} {()}
  lemma-[8b'] {jk = ₁₅} {₄₇} {₁₄} {()}
  lemma-[8b'] {jk = ₁₅} {₅₆} {₁₅} {()}
  lemma-[8b'] {jk = ₁₅} {₅₇} {₁₅} {()}
  lemma-[8b'] {jk = ₁₅} {₆₇} {₁₆} {()}
  lemma-[8b'] {jk = ₁₆} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₁₆} {₂₃} {₁₂} {₃₆} = by-basis-change (X₀₁ • X₀₆) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₆} {₂₄} {₁₂} {₄₆} = by-basis-change (X₀₁ • X₀₆ • X₃₄) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₆} {₂₅} {₁₂} {₅₆} = by-basis-change (X₀₁ • X₀₆ • X₃₄ • X₄₅) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₆} {₂₆} {₁₂} {()}
  lemma-[8b'] {jk = ₁₆} {₂₇} {₁₂} {()}
  lemma-[8b'] {jk = ₁₆} {₃₄} {₁₃} {₄₆} = by-basis-change (X₀₁ • X₀₆ • X₃₄ • X₂₃) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₆} {₃₅} {₁₃} {₅₆} = by-basis-change (X₀₁ • X₀₆ • X₃₅ • X₂₃) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₆} {₃₆} {₁₃} {()}
  lemma-[8b'] {jk = ₁₆} {₃₇} {₁₃} {()}
  lemma-[8b'] {jk = ₁₆} {₄₅} {₁₄} {₅₆} = by-basis-change (X₀₁ • X₀₆ • X₃₅ • X₂₃ • X₃₄) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₆} {₄₆} {₁₄} {()}
  lemma-[8b'] {jk = ₁₆} {₄₇} {₁₄} {()}
  lemma-[8b'] {jk = ₁₆} {₅₆} {₁₅} {()}
  lemma-[8b'] {jk = ₁₆} {₅₇} {₁₅} {()}
  lemma-[8b'] {jk = ₁₆} {₆₇} {₁₆} {()}
  lemma-[8b'] {jk = ₁₇} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₁₇} {₂₃} {₁₂} {₃₇} = by-basis-change (X₀₁ • X₀₇) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₂₄} {₁₂} {₄₇} = by-basis-change (X₀₁ • X₀₇ • X₃₄) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₂₅} {₁₂} {₅₇} = by-basis-change (X₀₁ • X₀₇ • X₃₄ • X₄₅) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₂₆} {₁₂} {₆₇} = by-basis-change (X₀₁ • X₀₇ • X₃₄ • X₄₆) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₂₇} {₁₂} {()}
  lemma-[8b'] {jk = ₁₇} {₃₄} {₁₃} {₄₇} = by-basis-change (X₀₁ • X₀₇ • X₃₄ • X₂₃) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₃₅} {₁₃} {₅₇} = by-basis-change (X₀₁ • X₀₇ • X₃₅ • X₂₃) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₃₆} {₁₃} {₆₇} = by-basis-change (X₀₁ • X₀₇ • X₃₆ • X₂₃) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₃₇} {₁₃} {()}
  lemma-[8b'] {jk = ₁₇} {₄₅} {₁₄} {₅₇} = by-basis-change (X₀₁ • X₀₇ • X₃₅ • X₂₃ • X₃₄) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₄₆} {₁₄} {₆₇} = by-basis-change (X₀₁ • X₀₇ • X₃₆ • X₂₃ • X₃₄) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₄₇} {₁₄} {()}
  lemma-[8b'] {jk = ₁₇} {₅₆} {₁₅} {₆₇} = by-basis-change (X₀₁ • X₀₇ • X₃₆ • X₂₃ • X₃₄ • X₄₅) (lemma-[S7a]'') 100 auto
  lemma-[8b'] {jk = ₁₇} {₅₇} {₁₅} {()}
  lemma-[8b'] {jk = ₁₇} {₆₇} {₁₆} {()}
  lemma-[8b'] {jk = ₂₃} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₂₃} {₃₄} {₂₃} {()}
  lemma-[8b'] {jk = ₂₃} {₃₅} {₂₃} {()}
  lemma-[8b'] {jk = ₂₃} {₃₆} {₂₃} {()}
  lemma-[8b'] {jk = ₂₃} {₃₇} {₂₃} {()}
  lemma-[8b'] {jk = ₂₃} {₄₅} {₂₄} {()}
  lemma-[8b'] {jk = ₂₃} {₄₆} {₂₄} {()}
  lemma-[8b'] {jk = ₂₃} {₄₇} {₂₄} {()}
  lemma-[8b'] {jk = ₂₃} {₅₆} {₂₅} {()}
  lemma-[8b'] {jk = ₂₃} {₅₇} {₂₅} {()}
  lemma-[8b'] {jk = ₂₃} {₆₇} {₂₆} {()}
  lemma-[8b'] {jk = ₂₄} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₂₄} {₃₄} {₂₃} {()}
  lemma-[8b'] {jk = ₂₄} {₃₅} {₂₃} {()}
  lemma-[8b'] {jk = ₂₄} {₃₆} {₂₃} {()}
  lemma-[8b'] {jk = ₂₄} {₃₇} {₂₃} {()}
  lemma-[8b'] {jk = ₂₄} {₄₅} {₂₄} {()}
  lemma-[8b'] {jk = ₂₄} {₄₆} {₂₄} {()}
  lemma-[8b'] {jk = ₂₄} {₄₇} {₂₄} {()}
  lemma-[8b'] {jk = ₂₄} {₅₆} {₂₅} {()}
  lemma-[8b'] {jk = ₂₄} {₅₇} {₂₅} {()}
  lemma-[8b'] {jk = ₂₄} {₆₇} {₂₆} {()}
  lemma-[8b'] {jk = ₂₅} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₂₅} {₃₄} {₂₃} {₄₅} = by-basis-change (X₁₂ • X₁₅) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₅} {₃₅} {₂₃} {()}
  lemma-[8b'] {jk = ₂₅} {₃₆} {₂₃} {()}
  lemma-[8b'] {jk = ₂₅} {₃₇} {₂₃} {()}
  lemma-[8b'] {jk = ₂₅} {₄₅} {₂₄} {()}
  lemma-[8b'] {jk = ₂₅} {₄₆} {₂₄} {()}
  lemma-[8b'] {jk = ₂₅} {₄₇} {₂₄} {()}
  lemma-[8b'] {jk = ₂₅} {₅₆} {₂₅} {()}
  lemma-[8b'] {jk = ₂₅} {₅₇} {₂₅} {()}
  lemma-[8b'] {jk = ₂₅} {₆₇} {₂₆} {()}
  lemma-[8b'] {jk = ₂₆} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₂₆} {₃₄} {₂₃} {₄₆} = by-basis-change (X₁₂ • X₁₆) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₆} {₃₅} {₂₃} {₅₆} = by-basis-change (X₁₂ • X₁₆ • X₄₅) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₆} {₃₆} {₂₃} {()}
  lemma-[8b'] {jk = ₂₆} {₃₇} {₂₃} {()}
  lemma-[8b'] {jk = ₂₆} {₄₅} {₂₄} {₅₆} = by-basis-change (X₁₂ • X₁₆ • X₄₅ • X₃₄) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₆} {₄₆} {₂₄} {()}
  lemma-[8b'] {jk = ₂₆} {₄₇} {₂₄} {()}
  lemma-[8b'] {jk = ₂₆} {₅₆} {₂₅} {()}
  lemma-[8b'] {jk = ₂₆} {₅₇} {₂₅} {()}
  lemma-[8b'] {jk = ₂₆} {₆₇} {₂₆} {()}
  lemma-[8b'] {jk = ₂₇} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₂₇} {₃₄} {₂₃} {₄₇} = by-basis-change (X₁₂ • X₁₇) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₇} {₃₅} {₂₃} {₅₇} = by-basis-change (X₁₂ • X₁₇ • X₄₅) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₇} {₃₆} {₂₃} {₆₇} = by-basis-change (X₁₂ • X₁₇ • X₄₆) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₇} {₃₇} {₂₃} {()}
  lemma-[8b'] {jk = ₂₇} {₄₅} {₂₄} {₅₇} = by-basis-change (X₁₂ • X₁₇ • X₄₅ • X₃₄) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₇} {₄₆} {₂₄} {₆₇} = by-basis-change (X₁₂ • X₁₇ • X₄₆ • X₃₄) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₇} {₄₇} {₂₄} {()}
  lemma-[8b'] {jk = ₂₇} {₅₆} {₂₅} {₆₇} = by-basis-change (X₁₂ • X₁₇ • X₄₆ • X₃₄ • X₄₅) (lemma-[S8f]'') 100 auto
  lemma-[8b'] {jk = ₂₇} {₅₇} {₂₅} {()}
  lemma-[8b'] {jk = ₂₇} {₆₇} {₂₆} {()}
  lemma-[8b'] {jk = ₃₄} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₃₄} {₄₅} {₃₄} {()}
  lemma-[8b'] {jk = ₃₄} {₄₆} {₃₄} {()}
  lemma-[8b'] {jk = ₃₄} {₄₇} {₃₄} {()}
  lemma-[8b'] {jk = ₃₄} {₅₆} {₃₅} {()}
  lemma-[8b'] {jk = ₃₄} {₅₇} {₃₅} {()}
  lemma-[8b'] {jk = ₃₄} {₆₇} {₃₆} {()}
  lemma-[8b'] {jk = ₃₅} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₃₅} {₄₅} {₃₄} {()}
  lemma-[8b'] {jk = ₃₅} {₄₆} {₃₄} {()}
  lemma-[8b'] {jk = ₃₅} {₄₇} {₃₄} {()}
  lemma-[8b'] {jk = ₃₅} {₅₆} {₃₅} {()}
  lemma-[8b'] {jk = ₃₅} {₅₇} {₃₅} {()}
  lemma-[8b'] {jk = ₃₅} {₆₇} {₃₆} {()}
  lemma-[8b'] {jk = ₃₆} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₃₆} {₄₅} {₃₄} {₅₆} = by-basis-change (X₂₃ • X₂₆) (lemma-[S8j]'') 100 auto
  lemma-[8b'] {jk = ₃₆} {₄₆} {₃₄} {()}
  lemma-[8b'] {jk = ₃₆} {₄₇} {₃₄} {()}
  lemma-[8b'] {jk = ₃₆} {₅₆} {₃₅} {()}
  lemma-[8b'] {jk = ₃₆} {₅₇} {₃₅} {()}
  lemma-[8b'] {jk = ₃₆} {₆₇} {₃₆} {()}
  lemma-[8b'] {jk = ₃₇} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₃₇} {₄₅} {₃₄} {₅₇} = by-basis-change (X₂₃ • X₂₇) (lemma-[S8j]'') 100 auto
  lemma-[8b'] {jk = ₃₇} {₄₆} {₃₄} {₆₇} = by-basis-change (X₂₃ • X₂₇ • X₅₆) (lemma-[S8j]'') 100 auto
  lemma-[8b'] {jk = ₃₇} {₄₇} {₃₄} {()}
  lemma-[8b'] {jk = ₃₇} {₅₆} {₃₅} {₆₇} = by-basis-change (X₂₃ • X₂₇ • X₅₆ • X₄₅) (lemma-[S8j]'') 100 auto
  lemma-[8b'] {jk = ₃₇} {₅₇} {₃₅} {()}
  lemma-[8b'] {jk = ₃₇} {₆₇} {₃₆} {()}
  lemma-[8b'] {jk = ₄₅} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₄₅} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₄₆} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₄₇} {()} {mk}
  lemma-[8b'] {jk = ₄₅} {₅₆} {₄₅} {()}
  lemma-[8b'] {jk = ₄₅} {₅₇} {₄₅} {()}
  lemma-[8b'] {jk = ₄₅} {₆₇} {₄₆} {()}
  lemma-[8b'] {jk = ₄₆} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₄₅} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₄₆} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₄₇} {()} {mk}
  lemma-[8b'] {jk = ₄₆} {₅₆} {₄₅} {()}
  lemma-[8b'] {jk = ₄₆} {₅₇} {₄₅} {()}
  lemma-[8b'] {jk = ₄₆} {₆₇} {₄₆} {()}
  lemma-[8b'] {jk = ₄₇} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₄₅} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₄₆} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₄₇} {()} {mk}
  lemma-[8b'] {jk = ₄₇} {₅₆} {₄₅} {₆₇} = by-basis-change (X₃₄ • X₃₇) (lemma-[S8m]'') 100 auto
  lemma-[8b'] {jk = ₄₇} {₅₇} {₄₅} {()}
  lemma-[8b'] {jk = ₄₇} {₆₇} {₄₆} {()}
  lemma-[8b'] {jk = ₅₆} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₄₅} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₄₆} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₄₇} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₅₆} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₅₇} {()} {mk}
  lemma-[8b'] {jk = ₅₆} {₆₇} {₅₆} {()}
  lemma-[8b'] {jk = ₅₇} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₄₅} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₄₆} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₄₇} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₅₆} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₅₇} {()} {mk}
  lemma-[8b'] {jk = ₅₇} {₆₇} {₅₆} {()}
  lemma-[8b'] {jk = ₆₇} {₀₁} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₀₂} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₀₃} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₀₄} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₀₅} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₀₆} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₀₇} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₁₂} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₁₃} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₁₄} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₁₅} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₁₆} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₁₇} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₂₃} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₂₄} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₂₅} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₂₆} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₂₇} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₃₄} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₃₅} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₃₆} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₃₇} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₄₅} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₄₆} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₄₇} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₅₆} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₅₇} {()} {mk}
  lemma-[8b'] {jk = ₆₇} {₆₇} {()} {mk}
