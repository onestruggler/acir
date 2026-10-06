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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax13 where

  lemma-[13] : ∀ {j k l} {kl : Less k l} -> {jk : Less j k} -> {jl : Less j l} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (K kl • X jk) === (g ʷ) (X jk • K jl)
  lemma-[13] {kl = ₀₁} {()} {jl}
  lemma-[13] {kl = ₀₂} {()} {jl}
  lemma-[13] {kl = ₀₃} {()} {jl}
  lemma-[13] {kl = ₀₄} {()} {jl}
  lemma-[13] {kl = ₀₅} {()} {jl}
  lemma-[13] {kl = ₀₆} {()} {jl}
  lemma-[13] {kl = ₀₇} {()} {jl}
  lemma-[13] {kl = ₁₂} {₀₁} {₀₂} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₁₃} {₀₁} {₀₃} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₁₄} {₀₁} {₀₄} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₁₅} {₀₁} {₀₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₁₆} {₀₁} {₀₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₁₇} {₀₁} {₀₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₃} {₀₂} {₀₃} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₃} {₁₂} {₁₃} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₄} {₀₂} {₀₄} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₄} {₁₂} {₁₄} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₅} {₀₂} {₀₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₅} {₁₂} {₁₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₆} {₀₂} {₀₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₆} {₁₂} {₁₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₇} {₀₂} {₀₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₂₇} {₁₂} {₁₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₄} {₀₃} {₀₄} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₄} {₁₃} {₁₄} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₄} {₂₃} {₂₄} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₅} {₀₃} {₀₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₅} {₁₃} {₁₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₅} {₂₃} {₂₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₆} {₀₃} {₀₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₆} {₁₃} {₁₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₆} {₂₃} {₂₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₇} {₀₃} {₀₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₇} {₁₃} {₁₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₃₇} {₂₃} {₂₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₅} {₀₄} {₀₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₅} {₁₄} {₁₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₅} {₂₄} {₂₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₅} {₃₄} {₃₅} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₆} {₀₄} {₀₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₆} {₁₄} {₁₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₆} {₂₄} {₂₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₆} {₃₄} {₃₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₇} {₀₄} {₀₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₇} {₁₄} {₁₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₇} {₂₄} {₂₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₄₇} {₃₄} {₃₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₆} {₀₅} {₀₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₆} {₁₅} {₁₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₆} {₂₅} {₂₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₆} {₃₅} {₃₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₆} {₄₅} {₄₆} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₇} {₀₅} {₀₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₇} {₁₅} {₁₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₇} {₂₅} {₂₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₇} {₃₅} {₃₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₅₇} {₄₅} {₄₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₆₇} {₀₆} {₀₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₆₇} {₁₆} {₁₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₆₇} {₂₆} {₂₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₆₇} {₃₆} {₃₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₆₇} {₄₆} {₄₇} = rewrite-stlu 100 auto
  lemma-[13] {kl = ₆₇} {₅₆} {₅₇} = rewrite-stlu 100 auto
