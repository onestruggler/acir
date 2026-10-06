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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax7c where

  lemma-[7c] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jl : Less j l} -> {mk : Less m k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (X jk • X lm) === (g ʷ) (X lm • X jk)
  lemma-[7c] {jk = ₀₁} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₀₁} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₀₁} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₀₁} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₀₁} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₀₁} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₀₁} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₀₁} {₁₂} {₀₁} {()}
  lemma-[7c] {jk = ₀₁} {₁₃} {₀₁} {()}
  lemma-[7c] {jk = ₀₁} {₁₄} {₀₁} {()}
  lemma-[7c] {jk = ₀₁} {₁₅} {₀₁} {()}
  lemma-[7c] {jk = ₀₁} {₁₆} {₀₁} {()}
  lemma-[7c] {jk = ₀₁} {₁₇} {₀₁} {()}
  lemma-[7c] {jk = ₀₁} {₂₃} {₀₂} {()}
  lemma-[7c] {jk = ₀₁} {₂₄} {₀₂} {()}
  lemma-[7c] {jk = ₀₁} {₂₅} {₀₂} {()}
  lemma-[7c] {jk = ₀₁} {₂₆} {₀₂} {()}
  lemma-[7c] {jk = ₀₁} {₂₇} {₀₂} {()}
  lemma-[7c] {jk = ₀₁} {₃₄} {₀₃} {()}
  lemma-[7c] {jk = ₀₁} {₃₅} {₀₃} {()}
  lemma-[7c] {jk = ₀₁} {₃₆} {₀₃} {()}
  lemma-[7c] {jk = ₀₁} {₃₇} {₀₃} {()}
  lemma-[7c] {jk = ₀₁} {₄₅} {₀₄} {()}
  lemma-[7c] {jk = ₀₁} {₄₆} {₀₄} {()}
  lemma-[7c] {jk = ₀₁} {₄₇} {₀₄} {()}
  lemma-[7c] {jk = ₀₁} {₅₆} {₀₅} {()}
  lemma-[7c] {jk = ₀₁} {₅₇} {₀₅} {()}
  lemma-[7c] {jk = ₀₁} {₆₇} {₀₆} {()}
  lemma-[7c] {jk = ₀₂} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₀₂} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₀₂} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₀₂} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₀₂} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₀₂} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₀₂} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₀₂} {₁₂} {₀₁} {()}
  lemma-[7c] {jk = ₀₂} {₁₃} {₀₁} {()}
  lemma-[7c] {jk = ₀₂} {₁₄} {₀₁} {()}
  lemma-[7c] {jk = ₀₂} {₁₅} {₀₁} {()}
  lemma-[7c] {jk = ₀₂} {₁₆} {₀₁} {()}
  lemma-[7c] {jk = ₀₂} {₁₇} {₀₁} {()}
  lemma-[7c] {jk = ₀₂} {₂₃} {₀₂} {()}
  lemma-[7c] {jk = ₀₂} {₂₄} {₀₂} {()}
  lemma-[7c] {jk = ₀₂} {₂₅} {₀₂} {()}
  lemma-[7c] {jk = ₀₂} {₂₆} {₀₂} {()}
  lemma-[7c] {jk = ₀₂} {₂₇} {₀₂} {()}
  lemma-[7c] {jk = ₀₂} {₃₄} {₀₃} {()}
  lemma-[7c] {jk = ₀₂} {₃₅} {₀₃} {()}
  lemma-[7c] {jk = ₀₂} {₃₆} {₀₃} {()}
  lemma-[7c] {jk = ₀₂} {₃₇} {₀₃} {()}
  lemma-[7c] {jk = ₀₂} {₄₅} {₀₄} {()}
  lemma-[7c] {jk = ₀₂} {₄₆} {₀₄} {()}
  lemma-[7c] {jk = ₀₂} {₄₇} {₀₄} {()}
  lemma-[7c] {jk = ₀₂} {₅₆} {₀₅} {()}
  lemma-[7c] {jk = ₀₂} {₅₇} {₀₅} {()}
  lemma-[7c] {jk = ₀₂} {₆₇} {₀₆} {()}
  lemma-[7c] {jk = ₀₃} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₀₃} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₀₃} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₀₃} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₀₃} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₀₃} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₀₃} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₀₃} {₁₂} {₀₁} {₂₃} = by-basis-change (X₀₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₃} {₁₃} {₀₁} {()}
  lemma-[7c] {jk = ₀₃} {₁₄} {₀₁} {()}
  lemma-[7c] {jk = ₀₃} {₁₅} {₀₁} {()}
  lemma-[7c] {jk = ₀₃} {₁₆} {₀₁} {()}
  lemma-[7c] {jk = ₀₃} {₁₇} {₀₁} {()}
  lemma-[7c] {jk = ₀₃} {₂₃} {₀₂} {()}
  lemma-[7c] {jk = ₀₃} {₂₄} {₀₂} {()}
  lemma-[7c] {jk = ₀₃} {₂₅} {₀₂} {()}
  lemma-[7c] {jk = ₀₃} {₂₆} {₀₂} {()}
  lemma-[7c] {jk = ₀₃} {₂₇} {₀₂} {()}
  lemma-[7c] {jk = ₀₃} {₃₄} {₀₃} {()}
  lemma-[7c] {jk = ₀₃} {₃₅} {₀₃} {()}
  lemma-[7c] {jk = ₀₃} {₃₆} {₀₃} {()}
  lemma-[7c] {jk = ₀₃} {₃₇} {₀₃} {()}
  lemma-[7c] {jk = ₀₃} {₄₅} {₀₄} {()}
  lemma-[7c] {jk = ₀₃} {₄₆} {₀₄} {()}
  lemma-[7c] {jk = ₀₃} {₄₇} {₀₄} {()}
  lemma-[7c] {jk = ₀₃} {₅₆} {₀₅} {()}
  lemma-[7c] {jk = ₀₃} {₅₇} {₀₅} {()}
  lemma-[7c] {jk = ₀₃} {₆₇} {₀₆} {()}
  lemma-[7c] {jk = ₀₄} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₀₄} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₀₄} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₀₄} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₀₄} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₀₄} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₀₄} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₀₄} {₁₂} {₀₁} {₂₄} = by-basis-change (X₀₂ • X₃₄) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₄} {₁₃} {₀₁} {₃₄} = by-basis-change (X₀₂ • X₃₄ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₄} {₁₄} {₀₁} {()}
  lemma-[7c] {jk = ₀₄} {₁₅} {₀₁} {()}
  lemma-[7c] {jk = ₀₄} {₁₆} {₀₁} {()}
  lemma-[7c] {jk = ₀₄} {₁₇} {₀₁} {()}
  lemma-[7c] {jk = ₀₄} {₂₃} {₀₂} {₃₄} = by-basis-change (X₀₂ • X₃₄ • X₂₃ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₄} {₂₄} {₀₂} {()}
  lemma-[7c] {jk = ₀₄} {₂₅} {₀₂} {()}
  lemma-[7c] {jk = ₀₄} {₂₆} {₀₂} {()}
  lemma-[7c] {jk = ₀₄} {₂₇} {₀₂} {()}
  lemma-[7c] {jk = ₀₄} {₃₄} {₀₃} {()}
  lemma-[7c] {jk = ₀₄} {₃₅} {₀₃} {()}
  lemma-[7c] {jk = ₀₄} {₃₆} {₀₃} {()}
  lemma-[7c] {jk = ₀₄} {₃₇} {₀₃} {()}
  lemma-[7c] {jk = ₀₄} {₄₅} {₀₄} {()}
  lemma-[7c] {jk = ₀₄} {₄₆} {₀₄} {()}
  lemma-[7c] {jk = ₀₄} {₄₇} {₀₄} {()}
  lemma-[7c] {jk = ₀₄} {₅₆} {₀₅} {()}
  lemma-[7c] {jk = ₀₄} {₅₇} {₀₅} {()}
  lemma-[7c] {jk = ₀₄} {₆₇} {₀₆} {()}
  lemma-[7c] {jk = ₀₅} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₀₅} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₀₅} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₀₅} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₀₅} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₀₅} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₀₅} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₀₅} {₁₂} {₀₁} {₂₅} = by-basis-change (X₀₂ • X₃₅) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₅} {₁₃} {₀₁} {₃₅} = by-basis-change (X₀₂ • X₃₅ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₅} {₁₄} {₀₁} {₄₅} = by-basis-change (X₀₂ • X₃₅ • X₂₄) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₅} {₁₅} {₀₁} {()}
  lemma-[7c] {jk = ₀₅} {₁₆} {₀₁} {()}
  lemma-[7c] {jk = ₀₅} {₁₇} {₀₁} {()}
  lemma-[7c] {jk = ₀₅} {₂₃} {₀₂} {₃₅} = by-basis-change (X₀₂ • X₃₅ • X₂₃ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₅} {₂₄} {₀₂} {₄₅} = by-basis-change (X₀₂ • X₃₅ • X₂₄ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₅} {₂₅} {₀₂} {()}
  lemma-[7c] {jk = ₀₅} {₂₆} {₀₂} {()}
  lemma-[7c] {jk = ₀₅} {₂₇} {₀₂} {()}
  lemma-[7c] {jk = ₀₅} {₃₄} {₀₃} {₄₅} = by-basis-change (X₀₂ • X₃₅ • X₂₄ • X₁₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₅} {₃₅} {₀₃} {()}
  lemma-[7c] {jk = ₀₅} {₃₆} {₀₃} {()}
  lemma-[7c] {jk = ₀₅} {₃₇} {₀₃} {()}
  lemma-[7c] {jk = ₀₅} {₄₅} {₀₄} {()}
  lemma-[7c] {jk = ₀₅} {₄₆} {₀₄} {()}
  lemma-[7c] {jk = ₀₅} {₄₇} {₀₄} {()}
  lemma-[7c] {jk = ₀₅} {₅₆} {₀₅} {()}
  lemma-[7c] {jk = ₀₅} {₅₇} {₀₅} {()}
  lemma-[7c] {jk = ₀₅} {₆₇} {₀₆} {()}
  lemma-[7c] {jk = ₀₆} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₀₆} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₀₆} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₀₆} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₀₆} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₀₆} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₀₆} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₀₆} {₁₂} {₀₁} {₂₆} = by-basis-change (X₀₂ • X₃₆) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₁₃} {₀₁} {₃₆} = by-basis-change (X₀₂ • X₃₆ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₁₄} {₀₁} {₄₆} = by-basis-change (X₀₂ • X₃₆ • X₂₄) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₁₅} {₀₁} {₅₆} = by-basis-change (X₀₂ • X₃₆ • X₂₅) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₁₆} {₀₁} {()}
  lemma-[7c] {jk = ₀₆} {₁₇} {₀₁} {()}
  lemma-[7c] {jk = ₀₆} {₂₃} {₀₂} {₃₆} = by-basis-change (X₀₂ • X₃₆ • X₂₃ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₂₄} {₀₂} {₄₆} = by-basis-change (X₀₂ • X₃₆ • X₂₄ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₂₅} {₀₂} {₅₆} = by-basis-change (X₀₂ • X₃₆ • X₂₅ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₂₆} {₀₂} {()}
  lemma-[7c] {jk = ₀₆} {₂₇} {₀₂} {()}
  lemma-[7c] {jk = ₀₆} {₃₄} {₀₃} {₄₆} = by-basis-change (X₀₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₃₅} {₀₃} {₅₆} = by-basis-change (X₀₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₃₆} {₀₃} {()}
  lemma-[7c] {jk = ₀₆} {₃₇} {₀₃} {()}
  lemma-[7c] {jk = ₀₆} {₄₅} {₀₄} {₅₆} = by-basis-change (X₀₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃ • X₃₄) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₆} {₄₆} {₀₄} {()}
  lemma-[7c] {jk = ₀₆} {₄₇} {₀₄} {()}
  lemma-[7c] {jk = ₀₆} {₅₆} {₀₅} {()}
  lemma-[7c] {jk = ₀₆} {₅₇} {₀₅} {()}
  lemma-[7c] {jk = ₀₆} {₆₇} {₀₆} {()}
  lemma-[7c] {jk = ₀₇} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₀₇} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₀₇} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₀₇} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₀₇} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₀₇} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₀₇} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₀₇} {₁₂} {₀₁} {₂₇} = by-basis-change (X₀₂ • X₃₇) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₁₃} {₀₁} {₃₇} = by-basis-change (X₀₂ • X₃₇ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₁₄} {₀₁} {₄₇} = by-basis-change (X₀₂ • X₃₇ • X₂₄) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₁₅} {₀₁} {₅₇} = by-basis-change (X₀₂ • X₃₇ • X₂₅) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₁₆} {₀₁} {₆₇} = by-basis-change (X₀₂ • X₃₇ • X₂₆) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₁₇} {₀₁} {()}
  lemma-[7c] {jk = ₀₇} {₂₃} {₀₂} {₃₇} = by-basis-change (X₀₂ • X₃₇ • X₂₃ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₂₄} {₀₂} {₄₇} = by-basis-change (X₀₂ • X₃₇ • X₂₄ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₂₅} {₀₂} {₅₇} = by-basis-change (X₀₂ • X₃₇ • X₂₅ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₂₆} {₀₂} {₆₇} = by-basis-change (X₀₂ • X₃₇ • X₂₆ • X₁₂) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₂₇} {₀₂} {()}
  lemma-[7c] {jk = ₀₇} {₃₄} {₀₃} {₄₇} = by-basis-change (X₀₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₃₅} {₀₃} {₅₇} = by-basis-change (X₀₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₃₆} {₀₃} {₆₇} = by-basis-change (X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₃₇} {₀₃} {()}
  lemma-[7c] {jk = ₀₇} {₄₅} {₀₄} {₅₇} = by-basis-change (X₀₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃ • X₃₄) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₄₆} {₀₄} {₆₇} = by-basis-change (X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₃₄) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₄₇} {₀₄} {()}
  lemma-[7c] {jk = ₀₇} {₅₆} {₀₅} {₆₇} = by-basis-change (X₀₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₃₄ • X₄₅) (axiom [S8a]) 100 auto
  lemma-[7c] {jk = ₀₇} {₅₇} {₀₅} {()}
  lemma-[7c] {jk = ₀₇} {₆₇} {₀₆} {()}
  lemma-[7c] {jk = ₁₂} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₁₂} {₂₃} {₁₂} {()}
  lemma-[7c] {jk = ₁₂} {₂₄} {₁₂} {()}
  lemma-[7c] {jk = ₁₂} {₂₅} {₁₂} {()}
  lemma-[7c] {jk = ₁₂} {₂₆} {₁₂} {()}
  lemma-[7c] {jk = ₁₂} {₂₇} {₁₂} {()}
  lemma-[7c] {jk = ₁₂} {₃₄} {₁₃} {()}
  lemma-[7c] {jk = ₁₂} {₃₅} {₁₃} {()}
  lemma-[7c] {jk = ₁₂} {₃₆} {₁₃} {()}
  lemma-[7c] {jk = ₁₂} {₃₇} {₁₃} {()}
  lemma-[7c] {jk = ₁₂} {₄₅} {₁₄} {()}
  lemma-[7c] {jk = ₁₂} {₄₆} {₁₄} {()}
  lemma-[7c] {jk = ₁₂} {₄₇} {₁₄} {()}
  lemma-[7c] {jk = ₁₂} {₅₆} {₁₅} {()}
  lemma-[7c] {jk = ₁₂} {₅₇} {₁₅} {()}
  lemma-[7c] {jk = ₁₂} {₆₇} {₁₆} {()}
  lemma-[7c] {jk = ₁₃} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₁₃} {₂₃} {₁₂} {()}
  lemma-[7c] {jk = ₁₃} {₂₄} {₁₂} {()}
  lemma-[7c] {jk = ₁₃} {₂₅} {₁₂} {()}
  lemma-[7c] {jk = ₁₃} {₂₆} {₁₂} {()}
  lemma-[7c] {jk = ₁₃} {₂₇} {₁₂} {()}
  lemma-[7c] {jk = ₁₃} {₃₄} {₁₃} {()}
  lemma-[7c] {jk = ₁₃} {₃₅} {₁₃} {()}
  lemma-[7c] {jk = ₁₃} {₃₆} {₁₃} {()}
  lemma-[7c] {jk = ₁₃} {₃₇} {₁₃} {()}
  lemma-[7c] {jk = ₁₃} {₄₅} {₁₄} {()}
  lemma-[7c] {jk = ₁₃} {₄₆} {₁₄} {()}
  lemma-[7c] {jk = ₁₃} {₄₇} {₁₄} {()}
  lemma-[7c] {jk = ₁₃} {₅₆} {₁₅} {()}
  lemma-[7c] {jk = ₁₃} {₅₇} {₁₅} {()}
  lemma-[7c] {jk = ₁₃} {₆₇} {₁₆} {()}
  lemma-[7c] {jk = ₁₄} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₁₄} {₂₃} {₁₂} {₃₄} = by-basis-change (X₀₄) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₄} {₂₄} {₁₂} {()}
  lemma-[7c] {jk = ₁₄} {₂₅} {₁₂} {()}
  lemma-[7c] {jk = ₁₄} {₂₆} {₁₂} {()}
  lemma-[7c] {jk = ₁₄} {₂₇} {₁₂} {()}
  lemma-[7c] {jk = ₁₄} {₃₄} {₁₃} {()}
  lemma-[7c] {jk = ₁₄} {₃₅} {₁₃} {()}
  lemma-[7c] {jk = ₁₄} {₃₆} {₁₃} {()}
  lemma-[7c] {jk = ₁₄} {₃₇} {₁₃} {()}
  lemma-[7c] {jk = ₁₄} {₄₅} {₁₄} {()}
  lemma-[7c] {jk = ₁₄} {₄₆} {₁₄} {()}
  lemma-[7c] {jk = ₁₄} {₄₇} {₁₄} {()}
  lemma-[7c] {jk = ₁₄} {₅₆} {₁₅} {()}
  lemma-[7c] {jk = ₁₄} {₅₇} {₁₅} {()}
  lemma-[7c] {jk = ₁₄} {₆₇} {₁₆} {()}
  lemma-[7c] {jk = ₁₅} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₁₅} {₂₃} {₁₂} {₃₅} = by-basis-change (X₀₅) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₅} {₂₄} {₁₂} {₄₅} = by-basis-change (X₀₅ • X₃₄) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₅} {₂₅} {₁₂} {()}
  lemma-[7c] {jk = ₁₅} {₂₆} {₁₂} {()}
  lemma-[7c] {jk = ₁₅} {₂₇} {₁₂} {()}
  lemma-[7c] {jk = ₁₅} {₃₄} {₁₃} {₄₅} = by-basis-change (X₀₅ • X₃₄ • X₂₃) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₅} {₃₅} {₁₃} {()}
  lemma-[7c] {jk = ₁₅} {₃₆} {₁₃} {()}
  lemma-[7c] {jk = ₁₅} {₃₇} {₁₃} {()}
  lemma-[7c] {jk = ₁₅} {₄₅} {₁₄} {()}
  lemma-[7c] {jk = ₁₅} {₄₆} {₁₄} {()}
  lemma-[7c] {jk = ₁₅} {₄₇} {₁₄} {()}
  lemma-[7c] {jk = ₁₅} {₅₆} {₁₅} {()}
  lemma-[7c] {jk = ₁₅} {₅₇} {₁₅} {()}
  lemma-[7c] {jk = ₁₅} {₆₇} {₁₆} {()}
  lemma-[7c] {jk = ₁₆} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₁₆} {₂₃} {₁₂} {₃₆} = by-basis-change (X₀₆) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₆} {₂₄} {₁₂} {₄₆} = by-basis-change (X₀₆ • X₃₄) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₆} {₂₅} {₁₂} {₅₆} = by-basis-change (X₀₆ • X₃₄ • X₄₅) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₆} {₂₆} {₁₂} {()}
  lemma-[7c] {jk = ₁₆} {₂₇} {₁₂} {()}
  lemma-[7c] {jk = ₁₆} {₃₄} {₁₃} {₄₆} = by-basis-change (X₀₆ • X₃₄ • X₂₃) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₆} {₃₅} {₁₃} {₅₆} = by-basis-change (X₀₆ • X₃₅ • X₂₃) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₆} {₃₆} {₁₃} {()}
  lemma-[7c] {jk = ₁₆} {₃₇} {₁₃} {()}
  lemma-[7c] {jk = ₁₆} {₄₅} {₁₄} {₅₆} = by-basis-change (X₀₆ • X₃₅ • X₂₃ • X₃₄) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₆} {₄₆} {₁₄} {()}
  lemma-[7c] {jk = ₁₆} {₄₇} {₁₄} {()}
  lemma-[7c] {jk = ₁₆} {₅₆} {₁₅} {()}
  lemma-[7c] {jk = ₁₆} {₅₇} {₁₅} {()}
  lemma-[7c] {jk = ₁₆} {₆₇} {₁₆} {()}
  lemma-[7c] {jk = ₁₇} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₁₇} {₂₃} {₁₂} {₃₇} = by-basis-change (X₀₇) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₂₄} {₁₂} {₄₇} = by-basis-change (X₀₇ • X₃₄) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₂₅} {₁₂} {₅₇} = by-basis-change (X₀₇ • X₃₄ • X₄₅) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₂₆} {₁₂} {₆₇} = by-basis-change (X₀₇ • X₃₄ • X₄₆) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₂₇} {₁₂} {()}
  lemma-[7c] {jk = ₁₇} {₃₄} {₁₃} {₄₇} = by-basis-change (X₀₇ • X₃₄ • X₂₃) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₃₅} {₁₃} {₅₇} = by-basis-change (X₀₇ • X₃₅ • X₂₃) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₃₆} {₁₃} {₆₇} = by-basis-change (X₀₇ • X₃₆ • X₂₃) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₃₇} {₁₃} {()}
  lemma-[7c] {jk = ₁₇} {₄₅} {₁₄} {₅₇} = by-basis-change (X₀₇ • X₃₅ • X₂₃ • X₃₄) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₄₆} {₁₄} {₆₇} = by-basis-change (X₀₇ • X₃₆ • X₂₃ • X₃₄) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₄₇} {₁₄} {()}
  lemma-[7c] {jk = ₁₇} {₅₆} {₁₅} {₆₇} = by-basis-change (X₀₇ • X₃₆ • X₂₃ • X₃₄ • X₄₅) (symm (axiom [S8a])) 100 auto
  lemma-[7c] {jk = ₁₇} {₅₇} {₁₅} {()}
  lemma-[7c] {jk = ₁₇} {₆₇} {₁₆} {()}
  lemma-[7c] {jk = ₂₃} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₂₃} {₃₄} {₂₃} {()}
  lemma-[7c] {jk = ₂₃} {₃₅} {₂₃} {()}
  lemma-[7c] {jk = ₂₃} {₃₆} {₂₃} {()}
  lemma-[7c] {jk = ₂₃} {₃₇} {₂₃} {()}
  lemma-[7c] {jk = ₂₃} {₄₅} {₂₄} {()}
  lemma-[7c] {jk = ₂₃} {₄₆} {₂₄} {()}
  lemma-[7c] {jk = ₂₃} {₄₇} {₂₄} {()}
  lemma-[7c] {jk = ₂₃} {₅₆} {₂₅} {()}
  lemma-[7c] {jk = ₂₃} {₅₇} {₂₅} {()}
  lemma-[7c] {jk = ₂₃} {₆₇} {₂₆} {()}
  lemma-[7c] {jk = ₂₄} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₂₄} {₃₄} {₂₃} {()}
  lemma-[7c] {jk = ₂₄} {₃₅} {₂₃} {()}
  lemma-[7c] {jk = ₂₄} {₃₆} {₂₃} {()}
  lemma-[7c] {jk = ₂₄} {₃₇} {₂₃} {()}
  lemma-[7c] {jk = ₂₄} {₄₅} {₂₄} {()}
  lemma-[7c] {jk = ₂₄} {₄₆} {₂₄} {()}
  lemma-[7c] {jk = ₂₄} {₄₇} {₂₄} {()}
  lemma-[7c] {jk = ₂₄} {₅₆} {₂₅} {()}
  lemma-[7c] {jk = ₂₄} {₅₇} {₂₅} {()}
  lemma-[7c] {jk = ₂₄} {₆₇} {₂₆} {()}
  lemma-[7c] {jk = ₂₅} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₂₅} {₃₄} {₂₃} {₄₅} = by-basis-change (X₁₅) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₅} {₃₅} {₂₃} {()}
  lemma-[7c] {jk = ₂₅} {₃₆} {₂₃} {()}
  lemma-[7c] {jk = ₂₅} {₃₇} {₂₃} {()}
  lemma-[7c] {jk = ₂₅} {₄₅} {₂₄} {()}
  lemma-[7c] {jk = ₂₅} {₄₆} {₂₄} {()}
  lemma-[7c] {jk = ₂₅} {₄₇} {₂₄} {()}
  lemma-[7c] {jk = ₂₅} {₅₆} {₂₅} {()}
  lemma-[7c] {jk = ₂₅} {₅₇} {₂₅} {()}
  lemma-[7c] {jk = ₂₅} {₆₇} {₂₆} {()}
  lemma-[7c] {jk = ₂₆} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₂₆} {₃₄} {₂₃} {₄₆} = by-basis-change (X₁₆) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₆} {₃₅} {₂₃} {₅₆} = by-basis-change (X₁₆ • X₄₅) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₆} {₃₆} {₂₃} {()}
  lemma-[7c] {jk = ₂₆} {₃₇} {₂₃} {()}
  lemma-[7c] {jk = ₂₆} {₄₅} {₂₄} {₅₆} = by-basis-change (X₁₆ • X₄₅ • X₃₄) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₆} {₄₆} {₂₄} {()}
  lemma-[7c] {jk = ₂₆} {₄₇} {₂₄} {()}
  lemma-[7c] {jk = ₂₆} {₅₆} {₂₅} {()}
  lemma-[7c] {jk = ₂₆} {₅₇} {₂₅} {()}
  lemma-[7c] {jk = ₂₆} {₆₇} {₂₆} {()}
  lemma-[7c] {jk = ₂₇} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₂₇} {₃₄} {₂₃} {₄₇} = by-basis-change (X₁₇) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₇} {₃₅} {₂₃} {₅₇} = by-basis-change (X₁₇ • X₄₅) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₇} {₃₆} {₂₃} {₆₇} = by-basis-change (X₁₇ • X₄₆) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₇} {₃₇} {₂₃} {()}
  lemma-[7c] {jk = ₂₇} {₄₅} {₂₄} {₅₇} = by-basis-change (X₁₇ • X₄₅ • X₃₄) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₇} {₄₆} {₂₄} {₆₇} = by-basis-change (X₁₇ • X₄₆ • X₃₄) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₇} {₄₇} {₂₄} {()}
  lemma-[7c] {jk = ₂₇} {₅₆} {₂₅} {₆₇} = by-basis-change (X₁₇ • X₄₆ • X₃₄ • X₄₅) (symm (axiom [S8f])) 100 auto
  lemma-[7c] {jk = ₂₇} {₅₇} {₂₅} {()}
  lemma-[7c] {jk = ₂₇} {₆₇} {₂₆} {()}
  lemma-[7c] {jk = ₃₄} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₃₄} {₄₅} {₃₄} {()}
  lemma-[7c] {jk = ₃₄} {₄₆} {₃₄} {()}
  lemma-[7c] {jk = ₃₄} {₄₇} {₃₄} {()}
  lemma-[7c] {jk = ₃₄} {₅₆} {₃₅} {()}
  lemma-[7c] {jk = ₃₄} {₅₇} {₃₅} {()}
  lemma-[7c] {jk = ₃₄} {₆₇} {₃₆} {()}
  lemma-[7c] {jk = ₃₅} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₃₅} {₄₅} {₃₄} {()}
  lemma-[7c] {jk = ₃₅} {₄₆} {₃₄} {()}
  lemma-[7c] {jk = ₃₅} {₄₇} {₃₄} {()}
  lemma-[7c] {jk = ₃₅} {₅₆} {₃₅} {()}
  lemma-[7c] {jk = ₃₅} {₅₇} {₃₅} {()}
  lemma-[7c] {jk = ₃₅} {₆₇} {₃₆} {()}
  lemma-[7c] {jk = ₃₆} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₃₆} {₄₅} {₃₄} {₅₆} = by-basis-change (X₂₆) (symm (axiom [S8j])) 100 auto
  lemma-[7c] {jk = ₃₆} {₄₆} {₃₄} {()}
  lemma-[7c] {jk = ₃₆} {₄₇} {₃₄} {()}
  lemma-[7c] {jk = ₃₆} {₅₆} {₃₅} {()}
  lemma-[7c] {jk = ₃₆} {₅₇} {₃₅} {()}
  lemma-[7c] {jk = ₃₆} {₆₇} {₃₆} {()}
  lemma-[7c] {jk = ₃₇} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₃₇} {₄₅} {₃₄} {₅₇} = by-basis-change (X₂₇) (symm (axiom [S8j])) 100 auto
  lemma-[7c] {jk = ₃₇} {₄₆} {₃₄} {₆₇} = by-basis-change (X₂₇ • X₅₆) (symm (axiom [S8j])) 100 auto
  lemma-[7c] {jk = ₃₇} {₄₇} {₃₄} {()}
  lemma-[7c] {jk = ₃₇} {₅₆} {₃₅} {₆₇} = by-basis-change (X₂₇ • X₅₆ • X₄₅) (symm (axiom [S8j])) 100 auto
  lemma-[7c] {jk = ₃₇} {₅₇} {₃₅} {()}
  lemma-[7c] {jk = ₃₇} {₆₇} {₃₆} {()}
  lemma-[7c] {jk = ₄₅} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₄₅} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₄₆} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₄₇} {()} {mk}
  lemma-[7c] {jk = ₄₅} {₅₆} {₄₅} {()}
  lemma-[7c] {jk = ₄₅} {₅₇} {₄₅} {()}
  lemma-[7c] {jk = ₄₅} {₆₇} {₄₆} {()}
  lemma-[7c] {jk = ₄₆} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₄₅} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₄₆} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₄₇} {()} {mk}
  lemma-[7c] {jk = ₄₆} {₅₆} {₄₅} {()}
  lemma-[7c] {jk = ₄₆} {₅₇} {₄₅} {()}
  lemma-[7c] {jk = ₄₆} {₆₇} {₄₆} {()}
  lemma-[7c] {jk = ₄₇} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₄₅} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₄₆} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₄₇} {()} {mk}
  lemma-[7c] {jk = ₄₇} {₅₆} {₄₅} {₆₇} = by-basis-change (X₃₇) (symm (axiom [S8m])) 100 auto
  lemma-[7c] {jk = ₄₇} {₅₇} {₄₅} {()}
  lemma-[7c] {jk = ₄₇} {₆₇} {₄₆} {()}
  lemma-[7c] {jk = ₅₆} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₄₅} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₄₆} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₄₇} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₅₆} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₅₇} {()} {mk}
  lemma-[7c] {jk = ₅₆} {₆₇} {₅₆} {()}
  lemma-[7c] {jk = ₅₇} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₄₅} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₄₆} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₄₇} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₅₆} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₅₇} {()} {mk}
  lemma-[7c] {jk = ₅₇} {₆₇} {₅₆} {()}
  lemma-[7c] {jk = ₆₇} {₀₁} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₀₂} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₀₃} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₀₄} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₀₅} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₀₆} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₀₇} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₁₂} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₁₃} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₁₄} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₁₅} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₁₆} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₁₇} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₂₃} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₂₄} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₂₅} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₂₆} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₂₇} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₃₄} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₃₅} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₃₆} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₃₇} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₄₅} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₄₆} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₄₇} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₅₆} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₅₇} {()} {mk}
  lemma-[7c] {jk = ₆₇} {₆₇} {()} {mk}
