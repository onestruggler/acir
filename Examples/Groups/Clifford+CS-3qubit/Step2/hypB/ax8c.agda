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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax8c where

  lemma-[S7a]' : TwoLevel-Simplified.Rel ⊢ X₀₁ • K₂₃ === K₂₃ • X₀₁
  lemma-[S7a]' = by-basis-change (X₀₂ • X₁₃) (axiom [S7a]) 100 auto


  lemma-[S8f]' : TwoLevel-Simplified.Rel ⊢ X₁₂ • K₃₄ === K₃₄ • X₁₂
  lemma-[S8f]' = by-basis-change (X₃₄ • X₁₄ • X₀₃) (axiom [S7a]) 100 auto

  lemma-[S8j]' : TwoLevel-Simplified.Rel ⊢ X₂₃ • K₄₅ === K₄₅ • X₂₃
  lemma-[S8j]' = by-basis-change (X₁₅ • X₀₄) (axiom [S7a]) 100 auto

  lemma-[S8m]' : TwoLevel-Simplified.Rel ⊢ X₃₄ • K₅₆ === K₅₆ • X₃₄
  lemma-[S8m]' = by-basis-change (X₂₄ • X₁₆ • X₀₅) (axiom [S7a]) 100 auto


  lemma-[8c] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Less j l} -> {mk : Less m k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (X jk • K lm) === (g ʷ) (K lm • X jk)
  lemma-[8c] {jk = ₀₁} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₀₁} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₀₁} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₀₁} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₀₁} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₀₁} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₀₁} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₀₁} {₁₂} {₀₁} {()}
  lemma-[8c] {jk = ₀₁} {₁₃} {₀₁} {()}
  lemma-[8c] {jk = ₀₁} {₁₄} {₀₁} {()}
  lemma-[8c] {jk = ₀₁} {₁₅} {₀₁} {()}
  lemma-[8c] {jk = ₀₁} {₁₆} {₀₁} {()}
  lemma-[8c] {jk = ₀₁} {₁₇} {₀₁} {()}
  lemma-[8c] {jk = ₀₁} {₂₃} {₀₂} {()}
  lemma-[8c] {jk = ₀₁} {₂₄} {₀₂} {()}
  lemma-[8c] {jk = ₀₁} {₂₅} {₀₂} {()}
  lemma-[8c] {jk = ₀₁} {₂₆} {₀₂} {()}
  lemma-[8c] {jk = ₀₁} {₂₇} {₀₂} {()}
  lemma-[8c] {jk = ₀₁} {₃₄} {₀₃} {()}
  lemma-[8c] {jk = ₀₁} {₃₅} {₀₃} {()}
  lemma-[8c] {jk = ₀₁} {₃₆} {₀₃} {()}
  lemma-[8c] {jk = ₀₁} {₃₇} {₀₃} {()}
  lemma-[8c] {jk = ₀₁} {₄₅} {₀₄} {()}
  lemma-[8c] {jk = ₀₁} {₄₆} {₀₄} {()}
  lemma-[8c] {jk = ₀₁} {₄₇} {₀₄} {()}
  lemma-[8c] {jk = ₀₁} {₅₆} {₀₅} {()}
  lemma-[8c] {jk = ₀₁} {₅₇} {₀₅} {()}
  lemma-[8c] {jk = ₀₁} {₆₇} {₀₆} {()}
  lemma-[8c] {jk = ₀₂} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₀₂} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₀₂} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₀₂} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₀₂} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₀₂} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₀₂} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₀₂} {₁₂} {₀₁} {()}
  lemma-[8c] {jk = ₀₂} {₁₃} {₀₁} {()}
  lemma-[8c] {jk = ₀₂} {₁₄} {₀₁} {()}
  lemma-[8c] {jk = ₀₂} {₁₅} {₀₁} {()}
  lemma-[8c] {jk = ₀₂} {₁₆} {₀₁} {()}
  lemma-[8c] {jk = ₀₂} {₁₇} {₀₁} {()}
  lemma-[8c] {jk = ₀₂} {₂₃} {₀₂} {()}
  lemma-[8c] {jk = ₀₂} {₂₄} {₀₂} {()}
  lemma-[8c] {jk = ₀₂} {₂₅} {₀₂} {()}
  lemma-[8c] {jk = ₀₂} {₂₆} {₀₂} {()}
  lemma-[8c] {jk = ₀₂} {₂₇} {₀₂} {()}
  lemma-[8c] {jk = ₀₂} {₃₄} {₀₃} {()}
  lemma-[8c] {jk = ₀₂} {₃₅} {₀₃} {()}
  lemma-[8c] {jk = ₀₂} {₃₆} {₀₃} {()}
  lemma-[8c] {jk = ₀₂} {₃₇} {₀₃} {()}
  lemma-[8c] {jk = ₀₂} {₄₅} {₀₄} {()}
  lemma-[8c] {jk = ₀₂} {₄₆} {₀₄} {()}
  lemma-[8c] {jk = ₀₂} {₄₇} {₀₄} {()}
  lemma-[8c] {jk = ₀₂} {₅₆} {₀₅} {()}
  lemma-[8c] {jk = ₀₂} {₅₇} {₀₅} {()}
  lemma-[8c] {jk = ₀₂} {₆₇} {₀₆} {()}
  lemma-[8c] {jk = ₀₃} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₀₃} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₀₃} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₀₃} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₀₃} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₀₃} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₀₃} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₀₃} {₁₂} {₀₁} {₂₃} = by-basis-change (X₀₁ • X₀₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₃} {₁₃} {₀₁} {()}
  lemma-[8c] {jk = ₀₃} {₁₄} {₀₁} {()}
  lemma-[8c] {jk = ₀₃} {₁₅} {₀₁} {()}
  lemma-[8c] {jk = ₀₃} {₁₆} {₀₁} {()}
  lemma-[8c] {jk = ₀₃} {₁₇} {₀₁} {()}
  lemma-[8c] {jk = ₀₃} {₂₃} {₀₂} {()}
  lemma-[8c] {jk = ₀₃} {₂₄} {₀₂} {()}
  lemma-[8c] {jk = ₀₃} {₂₅} {₀₂} {()}
  lemma-[8c] {jk = ₀₃} {₂₆} {₀₂} {()}
  lemma-[8c] {jk = ₀₃} {₂₇} {₀₂} {()}
  lemma-[8c] {jk = ₀₃} {₃₄} {₀₃} {()}
  lemma-[8c] {jk = ₀₃} {₃₅} {₀₃} {()}
  lemma-[8c] {jk = ₀₃} {₃₆} {₀₃} {()}
  lemma-[8c] {jk = ₀₃} {₃₇} {₀₃} {()}
  lemma-[8c] {jk = ₀₃} {₄₅} {₀₄} {()}
  lemma-[8c] {jk = ₀₃} {₄₆} {₀₄} {()}
  lemma-[8c] {jk = ₀₃} {₄₇} {₀₄} {()}
  lemma-[8c] {jk = ₀₃} {₅₆} {₀₅} {()}
  lemma-[8c] {jk = ₀₃} {₅₇} {₀₅} {()}
  lemma-[8c] {jk = ₀₃} {₆₇} {₀₆} {()}
  lemma-[8c] {jk = ₀₄} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₀₄} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₀₄} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₀₄} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₀₄} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₀₄} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₀₄} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₀₄} {₁₂} {₀₁} {₂₄} = by-basis-change (X₀₁ • X₀₂ • X₃₄) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₄} {₁₃} {₀₁} {₃₄} = by-basis-change (X₀₁ • X₀₂ • X₃₄ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₄} {₁₄} {₀₁} {()}
  lemma-[8c] {jk = ₀₄} {₁₅} {₀₁} {()}
  lemma-[8c] {jk = ₀₄} {₁₆} {₀₁} {()}
  lemma-[8c] {jk = ₀₄} {₁₇} {₀₁} {()}
  lemma-[8c] {jk = ₀₄} {₂₃} {₀₂} {₃₄} = by-basis-change (X₀₁ • X₀₂ • X₃₄ • X₂₃ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₄} {₂₄} {₀₂} {()}
  lemma-[8c] {jk = ₀₄} {₂₅} {₀₂} {()}
  lemma-[8c] {jk = ₀₄} {₂₆} {₀₂} {()}
  lemma-[8c] {jk = ₀₄} {₂₇} {₀₂} {()}
  lemma-[8c] {jk = ₀₄} {₃₄} {₀₃} {()}
  lemma-[8c] {jk = ₀₄} {₃₅} {₀₃} {()}
  lemma-[8c] {jk = ₀₄} {₃₆} {₀₃} {()}
  lemma-[8c] {jk = ₀₄} {₃₇} {₀₃} {()}
  lemma-[8c] {jk = ₀₄} {₄₅} {₀₄} {()}
  lemma-[8c] {jk = ₀₄} {₄₆} {₀₄} {()}
  lemma-[8c] {jk = ₀₄} {₄₇} {₀₄} {()}
  lemma-[8c] {jk = ₀₄} {₅₆} {₀₅} {()}
  lemma-[8c] {jk = ₀₄} {₅₇} {₀₅} {()}
  lemma-[8c] {jk = ₀₄} {₆₇} {₀₆} {()}
  lemma-[8c] {jk = ₀₅} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₀₅} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₀₅} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₀₅} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₀₅} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₀₅} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₀₅} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₀₅} {₁₂} {₀₁} {₂₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₅} {₁₃} {₀₁} {₃₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₅} {₁₄} {₀₁} {₄₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₄) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₅} {₁₅} {₀₁} {()}
  lemma-[8c] {jk = ₀₅} {₁₆} {₀₁} {()}
  lemma-[8c] {jk = ₀₅} {₁₇} {₀₁} {()}
  lemma-[8c] {jk = ₀₅} {₂₃} {₀₂} {₃₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₃ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₅} {₂₄} {₀₂} {₄₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₄ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₅} {₂₅} {₀₂} {()}
  lemma-[8c] {jk = ₀₅} {₂₆} {₀₂} {()}
  lemma-[8c] {jk = ₀₅} {₂₇} {₀₂} {()}
  lemma-[8c] {jk = ₀₅} {₃₄} {₀₃} {₄₅} = by-basis-change (X₀₁ • X₀₂ • X₃₅ • X₂₄ • X₁₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₅} {₃₅} {₀₃} {()}
  lemma-[8c] {jk = ₀₅} {₃₆} {₀₃} {()}
  lemma-[8c] {jk = ₀₅} {₃₇} {₀₃} {()}
  lemma-[8c] {jk = ₀₅} {₄₅} {₀₄} {()}
  lemma-[8c] {jk = ₀₅} {₄₆} {₀₄} {()}
  lemma-[8c] {jk = ₀₅} {₄₇} {₀₄} {()}
  lemma-[8c] {jk = ₀₅} {₅₆} {₀₅} {()}
  lemma-[8c] {jk = ₀₅} {₅₇} {₀₅} {()}
  lemma-[8c] {jk = ₀₅} {₆₇} {₀₆} {()}
  lemma-[8c] {jk = ₀₆} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₀₆} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₀₆} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₀₆} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₀₆} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₀₆} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₀₆} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₀₆} {₁₂} {₀₁} {₂₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₁₃} {₀₁} {₃₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₁₄} {₀₁} {₄₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₄) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₁₅} {₀₁} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₁₆} {₀₁} {()}
  lemma-[8c] {jk = ₀₆} {₁₇} {₀₁} {()}
  lemma-[8c] {jk = ₀₆} {₂₃} {₀₂} {₃₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₃ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₂₄} {₀₂} {₄₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₄ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₂₅} {₀₂} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₂₆} {₀₂} {()}
  lemma-[8c] {jk = ₀₆} {₂₇} {₀₂} {()}
  lemma-[8c] {jk = ₀₆} {₃₄} {₀₃} {₄₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₃₅} {₀₃} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₃₆} {₀₃} {()}
  lemma-[8c] {jk = ₀₆} {₃₇} {₀₃} {()}
  lemma-[8c] {jk = ₀₆} {₄₅} {₀₄} {₅₆} = by-basis-change (X₀₁ • X₀₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₆} {₄₆} {₀₄} {()}
  lemma-[8c] {jk = ₀₆} {₄₇} {₀₄} {()}
  lemma-[8c] {jk = ₀₆} {₅₆} {₀₅} {()}
  lemma-[8c] {jk = ₀₆} {₅₇} {₀₅} {()}
  lemma-[8c] {jk = ₀₆} {₆₇} {₀₆} {()}
  lemma-[8c] {jk = ₀₇} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₀₇} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₀₇} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₀₇} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₀₇} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₀₇} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₀₇} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₀₇} {₁₂} {₀₁} {₂₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₁₃} {₀₁} {₃₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₁₄} {₀₁} {₄₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₄) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₁₅} {₀₁} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₁₆} {₀₁} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₁₇} {₀₁} {()}
  lemma-[8c] {jk = ₀₇} {₂₃} {₀₂} {₃₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₃ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₂₄} {₀₂} {₄₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₄ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₂₅} {₀₂} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₂₆} {₀₂} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₂₇} {₀₂} {()}
  lemma-[8c] {jk = ₀₇} {₃₄} {₀₃} {₄₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₃₅} {₀₃} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₃₆} {₀₃} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₃₇} {₀₃} {()}
  lemma-[8c] {jk = ₀₇} {₄₅} {₀₄} {₅₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₄₆} {₀₄} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₃₄) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₄₇} {₀₄} {()}
  lemma-[8c] {jk = ₀₇} {₅₆} {₀₅} {₆₇} = by-basis-change (X₀₁ • X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S7a])) 100 auto
  lemma-[8c] {jk = ₀₇} {₅₇} {₀₅} {()}
  lemma-[8c] {jk = ₀₇} {₆₇} {₀₆} {()}
  lemma-[8c] {jk = ₁₂} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₁₂} {₂₃} {₁₂} {()}
  lemma-[8c] {jk = ₁₂} {₂₄} {₁₂} {()}
  lemma-[8c] {jk = ₁₂} {₂₅} {₁₂} {()}
  lemma-[8c] {jk = ₁₂} {₂₆} {₁₂} {()}
  lemma-[8c] {jk = ₁₂} {₂₇} {₁₂} {()}
  lemma-[8c] {jk = ₁₂} {₃₄} {₁₃} {()}
  lemma-[8c] {jk = ₁₂} {₃₅} {₁₃} {()}
  lemma-[8c] {jk = ₁₂} {₃₆} {₁₃} {()}
  lemma-[8c] {jk = ₁₂} {₃₇} {₁₃} {()}
  lemma-[8c] {jk = ₁₂} {₄₅} {₁₄} {()}
  lemma-[8c] {jk = ₁₂} {₄₆} {₁₄} {()}
  lemma-[8c] {jk = ₁₂} {₄₇} {₁₄} {()}
  lemma-[8c] {jk = ₁₂} {₅₆} {₁₅} {()}
  lemma-[8c] {jk = ₁₂} {₅₇} {₁₅} {()}
  lemma-[8c] {jk = ₁₂} {₆₇} {₁₆} {()}
  lemma-[8c] {jk = ₁₃} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₁₃} {₂₃} {₁₂} {()}
  lemma-[8c] {jk = ₁₃} {₂₄} {₁₂} {()}
  lemma-[8c] {jk = ₁₃} {₂₅} {₁₂} {()}
  lemma-[8c] {jk = ₁₃} {₂₆} {₁₂} {()}
  lemma-[8c] {jk = ₁₃} {₂₇} {₁₂} {()}
  lemma-[8c] {jk = ₁₃} {₃₄} {₁₃} {()}
  lemma-[8c] {jk = ₁₃} {₃₅} {₁₃} {()}
  lemma-[8c] {jk = ₁₃} {₃₆} {₁₃} {()}
  lemma-[8c] {jk = ₁₃} {₃₇} {₁₃} {()}
  lemma-[8c] {jk = ₁₃} {₄₅} {₁₄} {()}
  lemma-[8c] {jk = ₁₃} {₄₆} {₁₄} {()}
  lemma-[8c] {jk = ₁₃} {₄₇} {₁₄} {()}
  lemma-[8c] {jk = ₁₃} {₅₆} {₁₅} {()}
  lemma-[8c] {jk = ₁₃} {₅₇} {₁₅} {()}
  lemma-[8c] {jk = ₁₃} {₆₇} {₁₆} {()}
  lemma-[8c] {jk = ₁₄} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₁₄} {₂₃} {₁₂} {₃₄} = by-basis-change (X₀₁ • X₀₄) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₄} {₂₄} {₁₂} {()}
  lemma-[8c] {jk = ₁₄} {₂₅} {₁₂} {()}
  lemma-[8c] {jk = ₁₄} {₂₆} {₁₂} {()}
  lemma-[8c] {jk = ₁₄} {₂₇} {₁₂} {()}
  lemma-[8c] {jk = ₁₄} {₃₄} {₁₃} {()}
  lemma-[8c] {jk = ₁₄} {₃₅} {₁₃} {()}
  lemma-[8c] {jk = ₁₄} {₃₆} {₁₃} {()}
  lemma-[8c] {jk = ₁₄} {₃₇} {₁₃} {()}
  lemma-[8c] {jk = ₁₄} {₄₅} {₁₄} {()}
  lemma-[8c] {jk = ₁₄} {₄₆} {₁₄} {()}
  lemma-[8c] {jk = ₁₄} {₄₇} {₁₄} {()}
  lemma-[8c] {jk = ₁₄} {₅₆} {₁₅} {()}
  lemma-[8c] {jk = ₁₄} {₅₇} {₁₅} {()}
  lemma-[8c] {jk = ₁₄} {₆₇} {₁₆} {()}
  lemma-[8c] {jk = ₁₅} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₁₅} {₂₃} {₁₂} {₃₅} = by-basis-change (X₀₅) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₅} {₂₄} {₁₂} {₄₅} = by-basis-change (X₀₅ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₅} {₂₅} {₁₂} {()}
  lemma-[8c] {jk = ₁₅} {₂₆} {₁₂} {()}
  lemma-[8c] {jk = ₁₅} {₂₇} {₁₂} {()}
  lemma-[8c] {jk = ₁₅} {₃₄} {₁₃} {₄₅} = by-basis-change (X₀₅ • X₃₄ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₅} {₃₅} {₁₃} {()}
  lemma-[8c] {jk = ₁₅} {₃₆} {₁₃} {()}
  lemma-[8c] {jk = ₁₅} {₃₇} {₁₃} {()}
  lemma-[8c] {jk = ₁₅} {₄₅} {₁₄} {()}
  lemma-[8c] {jk = ₁₅} {₄₆} {₁₄} {()}
  lemma-[8c] {jk = ₁₅} {₄₇} {₁₄} {()}
  lemma-[8c] {jk = ₁₅} {₅₆} {₁₅} {()}
  lemma-[8c] {jk = ₁₅} {₅₇} {₁₅} {()}
  lemma-[8c] {jk = ₁₅} {₆₇} {₁₆} {()}
  lemma-[8c] {jk = ₁₆} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₁₆} {₂₃} {₁₂} {₃₆} = by-basis-change (X₀₆) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₆} {₂₄} {₁₂} {₄₆} = by-basis-change (X₀₆ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₆} {₂₅} {₁₂} {₅₆} = by-basis-change (X₀₆ • X₃₄ • X₄₅) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₆} {₂₆} {₁₂} {()}
  lemma-[8c] {jk = ₁₆} {₂₇} {₁₂} {()}
  lemma-[8c] {jk = ₁₆} {₃₄} {₁₃} {₄₆} = by-basis-change (X₀₆ • X₃₄ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₆} {₃₅} {₁₃} {₅₆} = by-basis-change (X₀₆ • X₃₅ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₆} {₃₆} {₁₃} {()}
  lemma-[8c] {jk = ₁₆} {₃₇} {₁₃} {()}
  lemma-[8c] {jk = ₁₆} {₄₅} {₁₄} {₅₆} = by-basis-change (X₀₆ • X₃₅ • X₂₃ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₆} {₄₆} {₁₄} {()}
  lemma-[8c] {jk = ₁₆} {₄₇} {₁₄} {()}
  lemma-[8c] {jk = ₁₆} {₅₆} {₁₅} {()}
  lemma-[8c] {jk = ₁₆} {₅₇} {₁₅} {()}
  lemma-[8c] {jk = ₁₆} {₆₇} {₁₆} {()}
  lemma-[8c] {jk = ₁₇} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₁₇} {₂₃} {₁₂} {₃₇} = by-basis-change (X₀₇) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₂₄} {₁₂} {₄₇} = by-basis-change (X₀₇ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₂₅} {₁₂} {₅₇} = by-basis-change (X₀₇ • X₃₄ • X₄₅) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₂₆} {₁₂} {₆₇} = by-basis-change (X₀₇ • X₃₄ • X₄₆) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₂₇} {₁₂} {()}
  lemma-[8c] {jk = ₁₇} {₃₄} {₁₃} {₄₇} = by-basis-change (X₀₇ • X₃₄ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₃₅} {₁₃} {₅₇} = by-basis-change (X₀₇ • X₃₅ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₃₆} {₁₃} {₆₇} = by-basis-change (X₀₇ • X₃₆ • X₂₃) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₃₇} {₁₃} {()}
  lemma-[8c] {jk = ₁₇} {₄₅} {₁₄} {₅₇} = by-basis-change (X₀₇ • X₃₅ • X₂₃ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₄₆} {₁₄} {₆₇} = by-basis-change (X₀₇ • X₃₆ • X₂₃ • X₃₄) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₄₇} {₁₄} {()}
  lemma-[8c] {jk = ₁₇} {₅₆} {₁₅} {₆₇} = by-basis-change (X₀₇ • X₃₆ • X₂₃ • X₃₄ • X₄₅) (lemma-[S7a]') 100 auto
  lemma-[8c] {jk = ₁₇} {₅₇} {₁₅} {()}
  lemma-[8c] {jk = ₁₇} {₆₇} {₁₆} {()}
  lemma-[8c] {jk = ₂₃} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₂₃} {₃₄} {₂₃} {()}
  lemma-[8c] {jk = ₂₃} {₃₅} {₂₃} {()}
  lemma-[8c] {jk = ₂₃} {₃₆} {₂₃} {()}
  lemma-[8c] {jk = ₂₃} {₃₇} {₂₃} {()}
  lemma-[8c] {jk = ₂₃} {₄₅} {₂₄} {()}
  lemma-[8c] {jk = ₂₃} {₄₆} {₂₄} {()}
  lemma-[8c] {jk = ₂₃} {₄₇} {₂₄} {()}
  lemma-[8c] {jk = ₂₃} {₅₆} {₂₅} {()}
  lemma-[8c] {jk = ₂₃} {₅₇} {₂₅} {()}
  lemma-[8c] {jk = ₂₃} {₆₇} {₂₆} {()}
  lemma-[8c] {jk = ₂₄} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₂₄} {₃₄} {₂₃} {()}
  lemma-[8c] {jk = ₂₄} {₃₅} {₂₃} {()}
  lemma-[8c] {jk = ₂₄} {₃₆} {₂₃} {()}
  lemma-[8c] {jk = ₂₄} {₃₇} {₂₃} {()}
  lemma-[8c] {jk = ₂₄} {₄₅} {₂₄} {()}
  lemma-[8c] {jk = ₂₄} {₄₆} {₂₄} {()}
  lemma-[8c] {jk = ₂₄} {₄₇} {₂₄} {()}
  lemma-[8c] {jk = ₂₄} {₅₆} {₂₅} {()}
  lemma-[8c] {jk = ₂₄} {₅₇} {₂₅} {()}
  lemma-[8c] {jk = ₂₄} {₆₇} {₂₆} {()}
  lemma-[8c] {jk = ₂₅} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₂₅} {₃₄} {₂₃} {₄₅} = by-basis-change (X₁₅) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₅} {₃₅} {₂₃} {()}
  lemma-[8c] {jk = ₂₅} {₃₆} {₂₃} {()}
  lemma-[8c] {jk = ₂₅} {₃₇} {₂₃} {()}
  lemma-[8c] {jk = ₂₅} {₄₅} {₂₄} {()}
  lemma-[8c] {jk = ₂₅} {₄₆} {₂₄} {()}
  lemma-[8c] {jk = ₂₅} {₄₇} {₂₄} {()}
  lemma-[8c] {jk = ₂₅} {₅₆} {₂₅} {()}
  lemma-[8c] {jk = ₂₅} {₅₇} {₂₅} {()}
  lemma-[8c] {jk = ₂₅} {₆₇} {₂₆} {()}
  lemma-[8c] {jk = ₂₆} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₂₆} {₃₄} {₂₃} {₄₆} = by-basis-change (X₁₆) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₆} {₃₅} {₂₃} {₅₆} = by-basis-change (X₁₆ • X₄₅) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₆} {₃₆} {₂₃} {()}
  lemma-[8c] {jk = ₂₆} {₃₇} {₂₃} {()}
  lemma-[8c] {jk = ₂₆} {₄₅} {₂₄} {₅₆} = by-basis-change (X₁₆ • X₄₅ • X₃₄) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₆} {₄₆} {₂₄} {()}
  lemma-[8c] {jk = ₂₆} {₄₇} {₂₄} {()}
  lemma-[8c] {jk = ₂₆} {₅₆} {₂₅} {()}
  lemma-[8c] {jk = ₂₆} {₅₇} {₂₅} {()}
  lemma-[8c] {jk = ₂₆} {₆₇} {₂₆} {()}
  lemma-[8c] {jk = ₂₇} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₂₇} {₃₄} {₂₃} {₄₇} = by-basis-change (X₁₇) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₇} {₃₅} {₂₃} {₅₇} = by-basis-change (X₁₇ • X₄₅) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₇} {₃₆} {₂₃} {₆₇} = by-basis-change (X₁₇ • X₄₆) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₇} {₃₇} {₂₃} {()}
  lemma-[8c] {jk = ₂₇} {₄₅} {₂₄} {₅₇} = by-basis-change (X₁₇ • X₄₅ • X₃₄) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₇} {₄₆} {₂₄} {₆₇} = by-basis-change (X₁₇ • X₄₆ • X₃₄) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₇} {₄₇} {₂₄} {()}
  lemma-[8c] {jk = ₂₇} {₅₆} {₂₅} {₆₇} = by-basis-change (X₁₇ • X₄₆ • X₃₄ • X₄₅) (lemma-[S8f]') 100 auto
  lemma-[8c] {jk = ₂₇} {₅₇} {₂₅} {()}
  lemma-[8c] {jk = ₂₇} {₆₇} {₂₆} {()}
  lemma-[8c] {jk = ₃₄} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₃₄} {₄₅} {₃₄} {()}
  lemma-[8c] {jk = ₃₄} {₄₆} {₃₄} {()}
  lemma-[8c] {jk = ₃₄} {₄₇} {₃₄} {()}
  lemma-[8c] {jk = ₃₄} {₅₆} {₃₅} {()}
  lemma-[8c] {jk = ₃₄} {₅₇} {₃₅} {()}
  lemma-[8c] {jk = ₃₄} {₆₇} {₃₆} {()}
  lemma-[8c] {jk = ₃₅} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₃₅} {₄₅} {₃₄} {()}
  lemma-[8c] {jk = ₃₅} {₄₆} {₃₄} {()}
  lemma-[8c] {jk = ₃₅} {₄₇} {₃₄} {()}
  lemma-[8c] {jk = ₃₅} {₅₆} {₃₅} {()}
  lemma-[8c] {jk = ₃₅} {₅₇} {₃₅} {()}
  lemma-[8c] {jk = ₃₅} {₆₇} {₃₆} {()}
  lemma-[8c] {jk = ₃₆} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₃₆} {₄₅} {₃₄} {₅₆} = by-basis-change (X₂₆) (lemma-[S8j]') 100 auto
  lemma-[8c] {jk = ₃₆} {₄₆} {₃₄} {()}
  lemma-[8c] {jk = ₃₆} {₄₇} {₃₄} {()}
  lemma-[8c] {jk = ₃₆} {₅₆} {₃₅} {()}
  lemma-[8c] {jk = ₃₆} {₅₇} {₃₅} {()}
  lemma-[8c] {jk = ₃₆} {₆₇} {₃₆} {()}
  lemma-[8c] {jk = ₃₇} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₃₇} {₄₅} {₃₄} {₅₇} = by-basis-change (X₂₇) (lemma-[S8j]') 100 auto
  lemma-[8c] {jk = ₃₇} {₄₆} {₃₄} {₆₇} = by-basis-change (X₂₇ • X₅₆) (lemma-[S8j]') 100 auto
  lemma-[8c] {jk = ₃₇} {₄₇} {₃₄} {()}
  lemma-[8c] {jk = ₃₇} {₅₆} {₃₅} {₆₇} = by-basis-change (X₂₇ • X₅₆ • X₄₅) (lemma-[S8j]') 100 auto
  lemma-[8c] {jk = ₃₇} {₅₇} {₃₅} {()}
  lemma-[8c] {jk = ₃₇} {₆₇} {₃₆} {()}
  lemma-[8c] {jk = ₄₅} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₄₅} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₄₆} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₄₇} {()} {mk}
  lemma-[8c] {jk = ₄₅} {₅₆} {₄₅} {()}
  lemma-[8c] {jk = ₄₅} {₅₇} {₄₅} {()}
  lemma-[8c] {jk = ₄₅} {₆₇} {₄₆} {()}
  lemma-[8c] {jk = ₄₆} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₄₅} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₄₆} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₄₇} {()} {mk}
  lemma-[8c] {jk = ₄₆} {₅₆} {₄₅} {()}
  lemma-[8c] {jk = ₄₆} {₅₇} {₄₅} {()}
  lemma-[8c] {jk = ₄₆} {₆₇} {₄₆} {()}
  lemma-[8c] {jk = ₄₇} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₄₅} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₄₆} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₄₇} {()} {mk}
  lemma-[8c] {jk = ₄₇} {₅₆} {₄₅} {₆₇} = by-basis-change (X₃₇) (lemma-[S8m]') 100 auto
  lemma-[8c] {jk = ₄₇} {₅₇} {₄₅} {()}
  lemma-[8c] {jk = ₄₇} {₆₇} {₄₆} {()}
  lemma-[8c] {jk = ₅₆} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₄₅} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₄₆} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₄₇} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₅₆} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₅₇} {()} {mk}
  lemma-[8c] {jk = ₅₆} {₆₇} {₅₆} {()}
  lemma-[8c] {jk = ₅₇} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₄₅} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₄₆} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₄₇} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₅₆} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₅₇} {()} {mk}
  lemma-[8c] {jk = ₅₇} {₆₇} {₅₆} {()}
  lemma-[8c] {jk = ₆₇} {₀₁} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₀₂} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₀₃} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₀₄} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₀₅} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₀₆} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₀₇} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₁₂} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₁₃} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₁₄} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₁₅} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₁₆} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₁₇} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₂₃} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₂₄} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₂₅} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₂₆} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₂₇} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₃₄} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₃₅} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₃₆} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₃₇} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₄₅} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₄₆} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₄₇} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₅₆} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₅₇} {()} {mk}
  lemma-[8c] {jk = ₆₇} {₆₇} {()} {mk}
