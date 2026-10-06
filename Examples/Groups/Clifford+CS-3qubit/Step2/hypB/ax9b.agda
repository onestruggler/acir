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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax9b where

  lemma-[9b] : ∀ {j k l m} {jk : Less j k} {lm : Less l m} -> {jm : Less j m} -> {mk : Less m k} -> {lj : Less l j} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (K jk • K lm) === (g ʷ) (K lm • K jk)
  lemma-[9b] {jk = ₀₁} {₀₁} {₀₁} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₀₂} {₀₂} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₀₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₀₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₀₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₀₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₀₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₁₂} {₀₂} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₁₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₁₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₁₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₁₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₁₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₂₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₂₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₂₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₂₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₂₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₃₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₃₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₃₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₃₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₄₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₄₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₄₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₅₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₅₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₁} {₆₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₀₁} {₀₁} {₁₂} {()}
  lemma-[9b] {jk = ₀₂} {₀₂} {₀₂} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₀₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₀₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₀₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₀₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₀₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₁₂} {₀₂} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₁₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₁₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₁₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₁₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₁₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₂₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₂₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₂₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₂₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₂₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₃₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₃₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₃₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₃₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₄₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₄₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₄₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₅₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₅₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₂} {₆₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₀₁} {₀₁} {₁₃} {()}
  lemma-[9b] {jk = ₀₃} {₀₂} {₀₂} {₂₃} {()}
  lemma-[9b] {jk = ₀₃} {₀₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₀₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₀₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₀₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₀₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₁₂} {₀₂} {₂₃} {()}
  lemma-[9b] {jk = ₀₃} {₁₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₁₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₁₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₁₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₁₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₂₃} {₀₃} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₂₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₂₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₂₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₂₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₃₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₃₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₃₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₃₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₄₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₄₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₄₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₅₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₅₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₃} {₆₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₀₁} {₀₁} {₁₄} {()}
  lemma-[9b] {jk = ₀₄} {₀₂} {₀₂} {₂₄} {()}
  lemma-[9b] {jk = ₀₄} {₀₃} {₀₃} {₃₄} {()}
  lemma-[9b] {jk = ₀₄} {₀₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₀₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₀₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₀₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₁₂} {₀₂} {₂₄} {()}
  lemma-[9b] {jk = ₀₄} {₁₃} {₀₃} {₃₄} {()}
  lemma-[9b] {jk = ₀₄} {₁₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₁₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₁₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₁₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₂₃} {₀₃} {₃₄} {()}
  lemma-[9b] {jk = ₀₄} {₂₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₂₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₂₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₂₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₃₄} {₀₄} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₃₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₃₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₃₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₄₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₄₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₄₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₅₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₅₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₄} {₆₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₀₁} {₀₁} {₁₅} {()}
  lemma-[9b] {jk = ₀₅} {₀₂} {₀₂} {₂₅} {()}
  lemma-[9b] {jk = ₀₅} {₀₃} {₀₃} {₃₅} {()}
  lemma-[9b] {jk = ₀₅} {₀₄} {₀₄} {₄₅} {()}
  lemma-[9b] {jk = ₀₅} {₀₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₀₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₀₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₁₂} {₀₂} {₂₅} {()}
  lemma-[9b] {jk = ₀₅} {₁₃} {₀₃} {₃₅} {()}
  lemma-[9b] {jk = ₀₅} {₁₄} {₀₄} {₄₅} {()}
  lemma-[9b] {jk = ₀₅} {₁₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₁₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₁₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₂₃} {₀₃} {₃₅} {()}
  lemma-[9b] {jk = ₀₅} {₂₄} {₀₄} {₄₅} {()}
  lemma-[9b] {jk = ₀₅} {₂₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₂₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₂₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₃₄} {₀₄} {₄₅} {()}
  lemma-[9b] {jk = ₀₅} {₃₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₃₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₃₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₄₅} {₀₅} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₄₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₄₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₅₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₅₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₅} {₆₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₀₁} {₀₁} {₁₆} {()}
  lemma-[9b] {jk = ₀₆} {₀₂} {₀₂} {₂₆} {()}
  lemma-[9b] {jk = ₀₆} {₀₃} {₀₃} {₃₆} {()}
  lemma-[9b] {jk = ₀₆} {₀₄} {₀₄} {₄₆} {()}
  lemma-[9b] {jk = ₀₆} {₀₅} {₀₅} {₅₆} {()}
  lemma-[9b] {jk = ₀₆} {₀₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₀₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₁₂} {₀₂} {₂₆} {()}
  lemma-[9b] {jk = ₀₆} {₁₃} {₀₃} {₃₆} {()}
  lemma-[9b] {jk = ₀₆} {₁₄} {₀₄} {₄₆} {()}
  lemma-[9b] {jk = ₀₆} {₁₅} {₀₅} {₅₆} {()}
  lemma-[9b] {jk = ₀₆} {₁₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₁₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₂₃} {₀₃} {₃₆} {()}
  lemma-[9b] {jk = ₀₆} {₂₄} {₀₄} {₄₆} {()}
  lemma-[9b] {jk = ₀₆} {₂₅} {₀₅} {₅₆} {()}
  lemma-[9b] {jk = ₀₆} {₂₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₂₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₃₄} {₀₄} {₄₆} {()}
  lemma-[9b] {jk = ₀₆} {₃₅} {₀₅} {₅₆} {()}
  lemma-[9b] {jk = ₀₆} {₃₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₃₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₄₅} {₀₅} {₅₆} {()}
  lemma-[9b] {jk = ₀₆} {₄₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₄₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₅₆} {₀₆} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₅₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₆} {₆₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₇} {₀₁} {₀₁} {₁₇} {()}
  lemma-[9b] {jk = ₀₇} {₀₂} {₀₂} {₂₇} {()}
  lemma-[9b] {jk = ₀₇} {₀₃} {₀₃} {₃₇} {()}
  lemma-[9b] {jk = ₀₇} {₀₄} {₀₄} {₄₇} {()}
  lemma-[9b] {jk = ₀₇} {₀₅} {₀₅} {₅₇} {()}
  lemma-[9b] {jk = ₀₇} {₀₆} {₀₆} {₆₇} {()}
  lemma-[9b] {jk = ₀₇} {₀₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₇} {₁₂} {₀₂} {₂₇} {()}
  lemma-[9b] {jk = ₀₇} {₁₃} {₀₃} {₃₇} {()}
  lemma-[9b] {jk = ₀₇} {₁₄} {₀₄} {₄₇} {()}
  lemma-[9b] {jk = ₀₇} {₁₅} {₀₅} {₅₇} {()}
  lemma-[9b] {jk = ₀₇} {₁₆} {₀₆} {₆₇} {()}
  lemma-[9b] {jk = ₀₇} {₁₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₇} {₂₃} {₀₃} {₃₇} {()}
  lemma-[9b] {jk = ₀₇} {₂₄} {₀₄} {₄₇} {()}
  lemma-[9b] {jk = ₀₇} {₂₅} {₀₅} {₅₇} {()}
  lemma-[9b] {jk = ₀₇} {₂₆} {₀₆} {₆₇} {()}
  lemma-[9b] {jk = ₀₇} {₂₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₇} {₃₄} {₀₄} {₄₇} {()}
  lemma-[9b] {jk = ₀₇} {₃₅} {₀₅} {₅₇} {()}
  lemma-[9b] {jk = ₀₇} {₃₆} {₀₆} {₆₇} {()}
  lemma-[9b] {jk = ₀₇} {₃₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₇} {₄₅} {₀₅} {₅₇} {()}
  lemma-[9b] {jk = ₀₇} {₄₆} {₀₆} {₆₇} {()}
  lemma-[9b] {jk = ₀₇} {₄₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₇} {₅₆} {₀₆} {₆₇} {()}
  lemma-[9b] {jk = ₀₇} {₅₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₀₇} {₆₇} {₀₇} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₁₂} {₀₂} {₁₂} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₀₃} {₁₃} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₀₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₀₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₀₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₀₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₁₂} {₁₂} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₁₃} {₁₃} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₁₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₁₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₁₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₁₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₂₃} {₁₃} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₂₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₂₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₂₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₂₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₃₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₃₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₃₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₃₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₄₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₄₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₄₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₅₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₅₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₂} {₆₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₁₃} {₀₂} {₁₂} {₂₃} {₀₁} = by-basis-change (X₁₂) (axiom [S6]) 100 auto

  lemma-[9b] {jk = ₁₃} {₀₃} {₁₃} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₀₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₀₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₀₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₀₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₁₂} {₁₂} {₂₃} {()}
  lemma-[9b] {jk = ₁₃} {₁₃} {₁₃} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₁₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₁₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₁₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₁₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₂₃} {₁₃} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₂₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₂₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₂₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₂₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₃₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₃₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₃₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₃₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₄₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₄₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₄₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₅₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₅₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₃} {₆₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₁₄} {₀₂} {₁₂} {₂₄} {₀₁} = by-basis-change (X₁₂ • X₃₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₄} {₀₃} {₁₃} {₃₄} {₀₁} = by-basis-change (X₁₂ • X₃₄ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₄} {₀₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₀₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₀₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₀₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₁₂} {₁₂} {₂₄} {()}
  lemma-[9b] {jk = ₁₄} {₁₃} {₁₃} {₃₄} {()}
  lemma-[9b] {jk = ₁₄} {₁₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₁₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₁₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₁₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₂₃} {₁₃} {₃₄} {()}
  lemma-[9b] {jk = ₁₄} {₂₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₂₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₂₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₂₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₃₄} {₁₄} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₃₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₃₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₃₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₄₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₄₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₄₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₅₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₅₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₄} {₆₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₁₅} {₀₂} {₁₂} {₂₅} {₀₁} = by-basis-change (X₁₂ • X₃₅) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₅} {₀₃} {₁₃} {₃₅} {₀₁} = by-basis-change (X₁₂ • X₃₅ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₅} {₀₄} {₁₄} {₄₅} {₀₁} = by-basis-change (X₁₂ • X₃₅ • X₂₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₅} {₀₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₀₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₀₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₁₂} {₁₂} {₂₅} {()}
  lemma-[9b] {jk = ₁₅} {₁₃} {₁₃} {₃₅} {()}
  lemma-[9b] {jk = ₁₅} {₁₄} {₁₄} {₄₅} {()}
  lemma-[9b] {jk = ₁₅} {₁₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₁₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₁₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₂₃} {₁₃} {₃₅} {()}
  lemma-[9b] {jk = ₁₅} {₂₄} {₁₄} {₄₅} {()}
  lemma-[9b] {jk = ₁₅} {₂₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₂₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₂₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₃₄} {₁₄} {₄₅} {()}
  lemma-[9b] {jk = ₁₅} {₃₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₃₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₃₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₄₅} {₁₅} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₄₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₄₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₅₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₅₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₅} {₆₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₁₆} {₀₂} {₁₂} {₂₆} {₀₁} = by-basis-change (X₁₂ • X₃₆) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₆} {₀₃} {₁₃} {₃₆} {₀₁} = by-basis-change (X₁₂ • X₃₆ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₆} {₀₄} {₁₄} {₄₆} {₀₁} = by-basis-change (X₁₂ • X₃₆ • X₂₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₆} {₀₅} {₁₅} {₅₆} {₀₁} = by-basis-change (X₁₂ • X₃₆ • X₂₅) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₆} {₀₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₀₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₁₂} {₁₂} {₂₆} {()}
  lemma-[9b] {jk = ₁₆} {₁₃} {₁₃} {₃₆} {()}
  lemma-[9b] {jk = ₁₆} {₁₄} {₁₄} {₄₆} {()}
  lemma-[9b] {jk = ₁₆} {₁₅} {₁₅} {₅₆} {()}
  lemma-[9b] {jk = ₁₆} {₁₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₁₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₂₃} {₁₃} {₃₆} {()}
  lemma-[9b] {jk = ₁₆} {₂₄} {₁₄} {₄₆} {()}
  lemma-[9b] {jk = ₁₆} {₂₅} {₁₅} {₅₆} {()}
  lemma-[9b] {jk = ₁₆} {₂₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₂₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₃₄} {₁₄} {₄₆} {()}
  lemma-[9b] {jk = ₁₆} {₃₅} {₁₅} {₅₆} {()}
  lemma-[9b] {jk = ₁₆} {₃₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₃₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₄₅} {₁₅} {₅₆} {()}
  lemma-[9b] {jk = ₁₆} {₄₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₄₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₅₆} {₁₆} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₅₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₆} {₆₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₇} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₁₇} {₀₂} {₁₂} {₂₇} {₀₁} = by-basis-change (X₁₂ • X₃₇) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₇} {₀₃} {₁₃} {₃₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₇} {₀₄} {₁₄} {₄₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₇} {₀₅} {₁₅} {₅₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₅) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₇} {₀₆} {₁₆} {₆₇} {₀₁} = by-basis-change (X₁₂ • X₃₇ • X₂₆) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₁₇} {₀₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₇} {₁₂} {₁₂} {₂₇} {()}
  lemma-[9b] {jk = ₁₇} {₁₃} {₁₃} {₃₇} {()}
  lemma-[9b] {jk = ₁₇} {₁₄} {₁₄} {₄₇} {()}
  lemma-[9b] {jk = ₁₇} {₁₅} {₁₅} {₅₇} {()}
  lemma-[9b] {jk = ₁₇} {₁₆} {₁₆} {₆₇} {()}
  lemma-[9b] {jk = ₁₇} {₁₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₇} {₂₃} {₁₃} {₃₇} {()}
  lemma-[9b] {jk = ₁₇} {₂₄} {₁₄} {₄₇} {()}
  lemma-[9b] {jk = ₁₇} {₂₅} {₁₅} {₅₇} {()}
  lemma-[9b] {jk = ₁₇} {₂₆} {₁₆} {₆₇} {()}
  lemma-[9b] {jk = ₁₇} {₂₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₇} {₃₄} {₁₄} {₄₇} {()}
  lemma-[9b] {jk = ₁₇} {₃₅} {₁₅} {₅₇} {()}
  lemma-[9b] {jk = ₁₇} {₃₆} {₁₆} {₆₇} {()}
  lemma-[9b] {jk = ₁₇} {₃₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₇} {₄₅} {₁₅} {₅₇} {()}
  lemma-[9b] {jk = ₁₇} {₄₆} {₁₆} {₆₇} {()}
  lemma-[9b] {jk = ₁₇} {₄₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₇} {₅₆} {₁₆} {₆₇} {()}
  lemma-[9b] {jk = ₁₇} {₅₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₁₇} {₆₇} {₁₇} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₃} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₃} {₀₃} {₂₃} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₀₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₀₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₀₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₀₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₃} {₁₃} {₂₃} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₁₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₁₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₁₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₁₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₂₃} {₂₃} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₂₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₂₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₂₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₂₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₃₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₃₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₃₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₃₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₄₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₄₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₄₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₅₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₅₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₃} {₆₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₄} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₄} {₀₃} {₂₃} {₃₄} {₀₂} = by-basis-change (X₁₂ • X₃₄ • X₂₃ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₄} {₀₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₀₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₀₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₀₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₄} {₁₃} {₂₃} {₃₄} {₁₂} = by-basis-change (X₁₂ • X₃₄ • X₂₃ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₄} {₁₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₁₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₁₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₁₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₂₃} {₂₃} {₃₄} {()}
  lemma-[9b] {jk = ₂₄} {₂₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₂₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₂₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₂₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₃₄} {₂₄} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₃₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₃₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₃₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₄₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₄₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₄₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₅₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₅₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₄} {₆₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₅} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₅} {₀₃} {₂₃} {₃₅} {₀₂} = by-basis-change (X₁₂ • X₃₅ • X₂₃ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₅} {₀₄} {₂₄} {₄₅} {₀₂} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₅} {₀₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₀₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₀₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₅} {₁₃} {₂₃} {₃₅} {₁₂} = by-basis-change (X₁₂ • X₃₅ • X₂₃ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₅} {₁₄} {₂₄} {₄₅} {₁₂} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₅} {₁₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₁₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₁₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₂₃} {₂₃} {₃₅} {()}
  lemma-[9b] {jk = ₂₅} {₂₄} {₂₄} {₄₅} {()}
  lemma-[9b] {jk = ₂₅} {₂₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₂₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₂₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₃₄} {₂₄} {₄₅} {()}
  lemma-[9b] {jk = ₂₅} {₃₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₃₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₃₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₄₅} {₂₅} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₄₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₄₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₅₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₅₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₅} {₆₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₆} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₆} {₀₃} {₂₃} {₃₆} {₀₂} = by-basis-change (X₁₂ • X₃₆ • X₂₃ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₆} {₀₄} {₂₄} {₄₆} {₀₂} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₆} {₀₅} {₂₅} {₅₆} {₀₂} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₆} {₀₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₀₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₆} {₁₃} {₂₃} {₃₆} {₁₂} = by-basis-change (X₁₂ • X₃₆ • X₂₃ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₆} {₁₄} {₂₄} {₄₆} {₁₂} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₆} {₁₅} {₂₅} {₅₆} {₁₂} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₆} {₁₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₁₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₂₃} {₂₃} {₃₆} {()}
  lemma-[9b] {jk = ₂₆} {₂₄} {₂₄} {₄₆} {()}
  lemma-[9b] {jk = ₂₆} {₂₅} {₂₅} {₅₆} {()}
  lemma-[9b] {jk = ₂₆} {₂₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₂₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₃₄} {₂₄} {₄₆} {()}
  lemma-[9b] {jk = ₂₆} {₃₅} {₂₅} {₅₆} {()}
  lemma-[9b] {jk = ₂₆} {₃₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₃₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₄₅} {₂₅} {₅₆} {()}
  lemma-[9b] {jk = ₂₆} {₄₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₄₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₅₆} {₂₆} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₅₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₆} {₆₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₇} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₇} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₇} {₀₃} {₂₃} {₃₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₃ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₀₄} {₂₄} {₄₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₀₅} {₂₅} {₅₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₀₆} {₂₆} {₆₇} {₀₂} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₀₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₇} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₂₇} {₁₃} {₂₃} {₃₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₃ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₁₄} {₂₄} {₄₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₁₅} {₂₅} {₅₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₁₆} {₂₆} {₆₇} {₁₂} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₂₇} {₁₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₇} {₂₃} {₂₃} {₃₇} {()}
  lemma-[9b] {jk = ₂₇} {₂₄} {₂₄} {₄₇} {()}
  lemma-[9b] {jk = ₂₇} {₂₅} {₂₅} {₅₇} {()}
  lemma-[9b] {jk = ₂₇} {₂₆} {₂₆} {₆₇} {()}
  lemma-[9b] {jk = ₂₇} {₂₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₇} {₃₄} {₂₄} {₄₇} {()}
  lemma-[9b] {jk = ₂₇} {₃₅} {₂₅} {₅₇} {()}
  lemma-[9b] {jk = ₂₇} {₃₆} {₂₆} {₆₇} {()}
  lemma-[9b] {jk = ₂₇} {₃₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₇} {₄₅} {₂₅} {₅₇} {()}
  lemma-[9b] {jk = ₂₇} {₄₆} {₂₆} {₆₇} {()}
  lemma-[9b] {jk = ₂₇} {₄₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₇} {₅₆} {₂₆} {₆₇} {()}
  lemma-[9b] {jk = ₂₇} {₅₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₂₇} {₆₇} {₂₇} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₄} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₄} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₄} {₀₄} {₃₄} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₀₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₀₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₀₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₄} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₄} {₁₄} {₃₄} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₁₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₁₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₁₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₄} {₂₄} {₃₄} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₂₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₂₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₂₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₃₄} {₃₄} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₃₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₃₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₃₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₄₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₄₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₄₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₅₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₅₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₄} {₆₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₅} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₅} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₅} {₀₄} {₃₄} {₄₅} {₀₃} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₅} {₀₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₀₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₀₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₅} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₅} {₁₄} {₃₄} {₄₅} {₁₃} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₂₃ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₅} {₁₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₁₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₁₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₅} {₂₄} {₃₄} {₄₅} {₂₃} = by-basis-change (X₁₂ • X₃₅ • X₂₄ • X₁₂ • X₂₃ • X₀₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₅} {₂₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₂₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₂₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₃₄} {₃₄} {₄₅} {()}
  lemma-[9b] {jk = ₃₅} {₃₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₃₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₃₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₄₅} {₃₅} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₄₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₄₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₅₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₅₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₅} {₆₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₆} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₆} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₆} {₀₄} {₃₄} {₄₆} {₀₃} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₆} {₀₅} {₃₅} {₅₆} {₀₃} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₆} {₀₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₀₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₆} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₆} {₁₄} {₃₄} {₄₆} {₁₃} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₆} {₁₅} {₃₅} {₅₆} {₁₃} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₆} {₁₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₁₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₆} {₂₄} {₃₄} {₄₆} {₂₃} = by-basis-change (X₁₂ • X₃₆ • X₂₄ • X₁₂ • X₂₃ • X₀₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₆} {₂₅} {₃₅} {₅₆} {₂₃} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₃ • X₀₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₆} {₂₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₂₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₃₄} {₃₄} {₄₆} {()}
  lemma-[9b] {jk = ₃₆} {₃₅} {₃₅} {₅₆} {()}
  lemma-[9b] {jk = ₃₆} {₃₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₃₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₄₅} {₃₅} {₅₆} {()}
  lemma-[9b] {jk = ₃₆} {₄₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₄₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₅₆} {₃₆} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₅₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₆} {₆₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₇} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₇} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₇} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₇} {₀₄} {₃₄} {₄₇} {₀₃} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₀₅} {₃₅} {₅₇} {₀₃} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₀₆} {₃₆} {₆₇} {₀₃} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₀₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₇} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₇} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₇} {₁₄} {₃₄} {₄₇} {₁₃} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₁₅} {₃₅} {₅₇} {₁₃} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₁₆} {₃₆} {₆₇} {₁₃} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₁₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₇} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₃₇} {₂₄} {₃₄} {₄₇} {₂₃} = by-basis-change (X₁₂ • X₃₇ • X₂₄ • X₁₂ • X₂₃ • X₀₁ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₂₅} {₃₅} {₅₇} {₂₃} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₃ • X₀₁ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₂₆} {₃₆} {₆₇} {₂₃} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₃ • X₀₁ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₃₇} {₂₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₇} {₃₄} {₃₄} {₄₇} {()}
  lemma-[9b] {jk = ₃₇} {₃₅} {₃₅} {₅₇} {()}
  lemma-[9b] {jk = ₃₇} {₃₆} {₃₆} {₆₇} {()}
  lemma-[9b] {jk = ₃₇} {₃₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₇} {₄₅} {₃₅} {₅₇} {()}
  lemma-[9b] {jk = ₃₇} {₄₆} {₃₆} {₆₇} {()}
  lemma-[9b] {jk = ₃₇} {₄₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₇} {₅₆} {₃₆} {₆₇} {()}
  lemma-[9b] {jk = ₃₇} {₅₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₃₇} {₆₇} {₃₇} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₀₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₀₅} {₄₅} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₀₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₀₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₁₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₁₅} {₄₅} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₁₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₁₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₂₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₂₅} {₄₅} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₂₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₂₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₃₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₅} {₃₅} {₄₅} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₃₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₃₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₄₅} {₄₅} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₄₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₄₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₅₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₅₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₅} {₆₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₀₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₀₅} {₄₅} {₅₆} {₀₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₆} {₀₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₀₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₁₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₁₅} {₄₅} {₅₆} {₁₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₆} {₁₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₁₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₂₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₂₅} {₄₅} {₅₆} {₂₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄ • X₀₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₆} {₂₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₂₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₃₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₆} {₃₅} {₄₅} {₅₆} {₃₄} = by-basis-change (X₁₂ • X₃₆ • X₂₅ • X₁₂ • X₂₄ • X₀₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₆} {₃₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₃₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₄₅} {₄₅} {₅₆} {()}
  lemma-[9b] {jk = ₄₆} {₄₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₄₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₅₆} {₄₆} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₅₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₆} {₆₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₇} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₀₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₀₅} {₄₅} {₅₇} {₀₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₀₆} {₄₆} {₆₇} {₀₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₀₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₇} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₁₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₁₅} {₄₅} {₅₇} {₁₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₁₆} {₄₆} {₆₇} {₁₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₁₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₇} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₂₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₂₅} {₄₅} {₅₇} {₂₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄ • X₀₁ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₂₆} {₄₆} {₆₇} {₂₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄ • X₀₁ • X₁₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₂₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₇} {₃₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₄₇} {₃₅} {₄₅} {₅₇} {₃₄} = by-basis-change (X₁₂ • X₃₇ • X₂₅ • X₁₂ • X₂₄ • X₀₁ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₃₆} {₄₆} {₆₇} {₃₄} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₄ • X₀₁ • X₁₂ • X₂₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₄₇} {₃₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₇} {₄₅} {₄₅} {₅₇} {()}
  lemma-[9b] {jk = ₄₇} {₄₆} {₄₆} {₆₇} {()}
  lemma-[9b] {jk = ₄₇} {₄₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₇} {₅₆} {₄₆} {₆₇} {()}
  lemma-[9b] {jk = ₄₇} {₅₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₄₇} {₆₇} {₄₇} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₀₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₀₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₀₆} {₅₆} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₀₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₁₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₁₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₁₆} {₅₆} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₁₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₂₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₂₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₂₆} {₅₆} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₂₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₃₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₃₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₃₆} {₅₆} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₃₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₄₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₆} {₄₆} {₅₆} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₄₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₅₆} {₅₆} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₅₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₆} {₆₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₇} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₀₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₀₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₀₆} {₅₆} {₆₇} {₀₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₅₇} {₀₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₇} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₁₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₁₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₁₆} {₅₆} {₆₇} {₁₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₁) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₅₇} {₁₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₇} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₂₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₂₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₂₆} {₅₆} {₆₇} {₂₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₂) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₅₇} {₂₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₇} {₃₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₃₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₃₆} {₅₆} {₆₇} {₃₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₃) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₅₇} {₃₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₇} {₄₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₅₇} {₄₆} {₅₆} {₆₇} {₄₅} = by-basis-change (X₁₂ • X₃₇ • X₂₆ • X₁₂ • X₂₅ • X₀₄) (axiom [S6]) 100 auto
  lemma-[9b] {jk = ₅₇} {₄₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₇} {₅₆} {₅₆} {₆₇} {()}
  lemma-[9b] {jk = ₅₇} {₅₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₅₇} {₆₇} {₅₇} {()} {lj}
  lemma-[9b] {jk = ₆₇} {₀₁} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₀₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₀₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₀₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₀₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₀₆} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₀₇} {₆₇} {()} {lj}
  lemma-[9b] {jk = ₆₇} {₁₂} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₁₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₁₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₁₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₁₆} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₁₇} {₆₇} {()} {lj}
  lemma-[9b] {jk = ₆₇} {₂₃} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₂₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₂₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₂₆} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₂₇} {₆₇} {()} {lj}
  lemma-[9b] {jk = ₆₇} {₃₄} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₃₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₃₆} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₃₇} {₆₇} {()} {lj}
  lemma-[9b] {jk = ₆₇} {₄₅} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₄₆} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₄₇} {₆₇} {()} {lj}
  lemma-[9b] {jk = ₆₇} {₅₆} {()} {mk} {lj}
  lemma-[9b] {jk = ₆₇} {₅₇} {₆₇} {()} {lj}
  lemma-[9b] {jk = ₆₇} {₆₇} {₆₇} {()} {lj}

