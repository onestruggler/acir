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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax14 where

  lemma-[14] : ∀ {j k l} {jl : Less j l} -> {kl : Less k l} -> {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (K jl • X kl) === (g ʷ) (X kl • K jk)
  lemma-[14] {jl = ₀₁} {₀₁} {()}
  lemma-[14] {jl = ₀₂} {₀₂} {()}
  lemma-[14] {jl = ₀₂} {₁₂} {₀₁} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₃} {₀₃} {()}
  lemma-[14] {jl = ₀₃} {₁₃} {₀₁} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₃} {₂₃} {₀₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₄} {₀₄} {()}
  lemma-[14] {jl = ₀₄} {₁₄} {₀₁} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₄} {₂₄} {₀₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₄} {₃₄} {₀₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₅} {₀₅} {()}
  lemma-[14] {jl = ₀₅} {₁₅} {₀₁} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₅} {₂₅} {₀₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₅} {₃₅} {₀₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₅} {₄₅} {₀₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₆} {₀₆} {()}
  lemma-[14] {jl = ₀₆} {₁₆} {₀₁} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₆} {₂₆} {₀₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₆} {₃₆} {₀₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₆} {₄₆} {₀₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₆} {₅₆} {₀₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₇} {₀₇} {()}
  lemma-[14] {jl = ₀₇} {₁₇} {₀₁} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₇} {₂₇} {₀₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₇} {₃₇} {₀₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₇} {₄₇} {₀₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₇} {₅₇} {₀₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₀₇} {₆₇} {₀₆} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₂} {₀₂} {()}
  lemma-[14] {jl = ₁₂} {₁₂} {()}
  lemma-[14] {jl = ₁₃} {₀₃} {()}
  lemma-[14] {jl = ₁₃} {₁₃} {()}
  lemma-[14] {jl = ₁₃} {₂₃} {₁₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₄} {₀₄} {()}
  lemma-[14] {jl = ₁₄} {₁₄} {()}
  lemma-[14] {jl = ₁₄} {₂₄} {₁₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₄} {₃₄} {₁₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₅} {₀₅} {()}
  lemma-[14] {jl = ₁₅} {₁₅} {()}
  lemma-[14] {jl = ₁₅} {₂₅} {₁₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₅} {₃₅} {₁₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₅} {₄₅} {₁₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₆} {₀₆} {()}
  lemma-[14] {jl = ₁₆} {₁₆} {()}
  lemma-[14] {jl = ₁₆} {₂₆} {₁₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₆} {₃₆} {₁₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₆} {₄₆} {₁₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₆} {₅₆} {₁₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₇} {₀₇} {()}
  lemma-[14] {jl = ₁₇} {₁₇} {()}
  lemma-[14] {jl = ₁₇} {₂₇} {₁₂} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₇} {₃₇} {₁₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₇} {₄₇} {₁₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₇} {₅₇} {₁₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₁₇} {₆₇} {₁₆} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₃} {₀₃} {()}
  lemma-[14] {jl = ₂₃} {₁₃} {()}
  lemma-[14] {jl = ₂₃} {₂₃} {()}
  lemma-[14] {jl = ₂₄} {₀₄} {()}
  lemma-[14] {jl = ₂₄} {₁₄} {()}
  lemma-[14] {jl = ₂₄} {₂₄} {()}
  lemma-[14] {jl = ₂₄} {₃₄} {₂₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₅} {₀₅} {()}
  lemma-[14] {jl = ₂₅} {₁₅} {()}
  lemma-[14] {jl = ₂₅} {₂₅} {()}
  lemma-[14] {jl = ₂₅} {₃₅} {₂₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₅} {₄₅} {₂₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₆} {₀₆} {()}
  lemma-[14] {jl = ₂₆} {₁₆} {()}
  lemma-[14] {jl = ₂₆} {₂₆} {()}
  lemma-[14] {jl = ₂₆} {₃₆} {₂₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₆} {₄₆} {₂₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₆} {₅₆} {₂₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₇} {₀₇} {()}
  lemma-[14] {jl = ₂₇} {₁₇} {()}
  lemma-[14] {jl = ₂₇} {₂₇} {()}
  lemma-[14] {jl = ₂₇} {₃₇} {₂₃} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₇} {₄₇} {₂₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₇} {₅₇} {₂₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₂₇} {₆₇} {₂₆} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₃₄} {₀₄} {()}
  lemma-[14] {jl = ₃₄} {₁₄} {()}
  lemma-[14] {jl = ₃₄} {₂₄} {()}
  lemma-[14] {jl = ₃₄} {₃₄} {()}
  lemma-[14] {jl = ₃₅} {₀₅} {()}
  lemma-[14] {jl = ₃₅} {₁₅} {()}
  lemma-[14] {jl = ₃₅} {₂₅} {()}
  lemma-[14] {jl = ₃₅} {₃₅} {()}
  lemma-[14] {jl = ₃₅} {₄₅} {₃₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₃₆} {₀₆} {()}
  lemma-[14] {jl = ₃₆} {₁₆} {()}
  lemma-[14] {jl = ₃₆} {₂₆} {()}
  lemma-[14] {jl = ₃₆} {₃₆} {()}
  lemma-[14] {jl = ₃₆} {₄₆} {₃₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₃₆} {₅₆} {₃₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₃₇} {₀₇} {()}
  lemma-[14] {jl = ₃₇} {₁₇} {()}
  lemma-[14] {jl = ₃₇} {₂₇} {()}
  lemma-[14] {jl = ₃₇} {₃₇} {()}
  lemma-[14] {jl = ₃₇} {₄₇} {₃₄} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₃₇} {₅₇} {₃₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₃₇} {₆₇} {₃₆} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₄₅} {₀₅} {()}
  lemma-[14] {jl = ₄₅} {₁₅} {()}
  lemma-[14] {jl = ₄₅} {₂₅} {()}
  lemma-[14] {jl = ₄₅} {₃₅} {()}
  lemma-[14] {jl = ₄₅} {₄₅} {()}
  lemma-[14] {jl = ₄₆} {₀₆} {()}
  lemma-[14] {jl = ₄₆} {₁₆} {()}
  lemma-[14] {jl = ₄₆} {₂₆} {()}
  lemma-[14] {jl = ₄₆} {₃₆} {()}
  lemma-[14] {jl = ₄₆} {₄₆} {()}
  lemma-[14] {jl = ₄₆} {₅₆} {₄₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₄₇} {₀₇} {()}
  lemma-[14] {jl = ₄₇} {₁₇} {()}
  lemma-[14] {jl = ₄₇} {₂₇} {()}
  lemma-[14] {jl = ₄₇} {₃₇} {()}
  lemma-[14] {jl = ₄₇} {₄₇} {()}
  lemma-[14] {jl = ₄₇} {₅₇} {₄₅} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₄₇} {₆₇} {₄₆} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₅₆} {₀₆} {()}
  lemma-[14] {jl = ₅₆} {₁₆} {()}
  lemma-[14] {jl = ₅₆} {₂₆} {()}
  lemma-[14] {jl = ₅₆} {₃₆} {()}
  lemma-[14] {jl = ₅₆} {₄₆} {()}
  lemma-[14] {jl = ₅₆} {₅₆} {()}
  lemma-[14] {jl = ₅₇} {₀₇} {()}
  lemma-[14] {jl = ₅₇} {₁₇} {()}
  lemma-[14] {jl = ₅₇} {₂₇} {()}
  lemma-[14] {jl = ₅₇} {₃₇} {()}
  lemma-[14] {jl = ₅₇} {₄₇} {()}
  lemma-[14] {jl = ₅₇} {₅₇} {()}
  lemma-[14] {jl = ₅₇} {₆₇} {₅₆} = rewrite-stlu 100 auto
  lemma-[14] {jl = ₆₇} {₀₇} {()}
  lemma-[14] {jl = ₆₇} {₁₇} {()}
  lemma-[14] {jl = ₆₇} {₂₇} {()}
  lemma-[14] {jl = ₆₇} {₃₇} {()}
  lemma-[14] {jl = ₆₇} {₄₇} {()}
  lemma-[14] {jl = ₆₇} {₅₇} {()}
  lemma-[14] {jl = ₆₇} {₆₇} {()}
