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

open import Examples.Groups.Clifford+CS-3qubit.Step2.Lafont-S8
open import Examples.Groups.Clifford+CS-3qubit.CosetNF

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax12 where

  lemma-[12] : ∀ {j k l} {jl : Less j l} -> {kl : Less k l} -> {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (X jl • X kl) === (g ʷ) (X kl • X jk)
  lemma-[12] {jl = ₀₁} {₀₁} {()}
  lemma-[12] {jl = ₀₂} {₀₂} {()}
  lemma-[12] {jl = ₀₂} {₁₂} {₀₁} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₃} {₀₃} {()}
  lemma-[12] {jl = ₀₃} {₁₃} {₀₁} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₃} {₂₃} {₀₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₄} {₀₄} {()}
  lemma-[12] {jl = ₀₄} {₁₄} {₀₁} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₄} {₂₄} {₀₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₄} {₃₄} {₀₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₅} {₀₅} {()}
  lemma-[12] {jl = ₀₅} {₁₅} {₀₁} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₅} {₂₅} {₀₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₅} {₃₅} {₀₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₅} {₄₅} {₀₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₆} {₀₆} {()}
  lemma-[12] {jl = ₀₆} {₁₆} {₀₁} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₆} {₂₆} {₀₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₆} {₃₆} {₀₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₆} {₄₆} {₀₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₆} {₅₆} {₀₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₇} {₀₇} {()}
  lemma-[12] {jl = ₀₇} {₁₇} {₀₁} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₇} {₂₇} {₀₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₇} {₃₇} {₀₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₇} {₄₇} {₀₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₇} {₅₇} {₀₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₀₇} {₆₇} {₀₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₂} {₀₂} {()}
  lemma-[12] {jl = ₁₂} {₁₂} {()}
  lemma-[12] {jl = ₁₃} {₀₃} {()}
  lemma-[12] {jl = ₁₃} {₁₃} {()}
  lemma-[12] {jl = ₁₃} {₂₃} {₁₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₄} {₀₄} {()}
  lemma-[12] {jl = ₁₄} {₁₄} {()}
  lemma-[12] {jl = ₁₄} {₂₄} {₁₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₄} {₃₄} {₁₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₅} {₀₅} {()}
  lemma-[12] {jl = ₁₅} {₁₅} {()}
  lemma-[12] {jl = ₁₅} {₂₅} {₁₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₅} {₃₅} {₁₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₅} {₄₅} {₁₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₆} {₀₆} {()}
  lemma-[12] {jl = ₁₆} {₁₆} {()}
  lemma-[12] {jl = ₁₆} {₂₆} {₁₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₆} {₃₆} {₁₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₆} {₄₆} {₁₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₆} {₅₆} {₁₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₇} {₀₇} {()}
  lemma-[12] {jl = ₁₇} {₁₇} {()}
  lemma-[12] {jl = ₁₇} {₂₇} {₁₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₇} {₃₇} {₁₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₇} {₄₇} {₁₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₇} {₅₇} {₁₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₁₇} {₆₇} {₁₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₃} {₀₃} {()}
  lemma-[12] {jl = ₂₃} {₁₃} {()}
  lemma-[12] {jl = ₂₃} {₂₃} {()}
  lemma-[12] {jl = ₂₄} {₀₄} {()}
  lemma-[12] {jl = ₂₄} {₁₄} {()}
  lemma-[12] {jl = ₂₄} {₂₄} {()}
  lemma-[12] {jl = ₂₄} {₃₄} {₂₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₅} {₀₅} {()}
  lemma-[12] {jl = ₂₅} {₁₅} {()}
  lemma-[12] {jl = ₂₅} {₂₅} {()}
  lemma-[12] {jl = ₂₅} {₃₅} {₂₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₅} {₄₅} {₂₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₆} {₀₆} {()}
  lemma-[12] {jl = ₂₆} {₁₆} {()}
  lemma-[12] {jl = ₂₆} {₂₆} {()}
  lemma-[12] {jl = ₂₆} {₃₆} {₂₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₆} {₄₆} {₂₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₆} {₅₆} {₂₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₇} {₀₇} {()}
  lemma-[12] {jl = ₂₇} {₁₇} {()}
  lemma-[12] {jl = ₂₇} {₂₇} {()}
  lemma-[12] {jl = ₂₇} {₃₇} {₂₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₇} {₄₇} {₂₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₇} {₅₇} {₂₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₂₇} {₆₇} {₂₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₃₄} {₀₄} {()}
  lemma-[12] {jl = ₃₄} {₁₄} {()}
  lemma-[12] {jl = ₃₄} {₂₄} {()}
  lemma-[12] {jl = ₃₄} {₃₄} {()}
  lemma-[12] {jl = ₃₅} {₀₅} {()}
  lemma-[12] {jl = ₃₅} {₁₅} {()}
  lemma-[12] {jl = ₃₅} {₂₅} {()}
  lemma-[12] {jl = ₃₅} {₃₅} {()}
  lemma-[12] {jl = ₃₅} {₄₅} {₃₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₃₆} {₀₆} {()}
  lemma-[12] {jl = ₃₆} {₁₆} {()}
  lemma-[12] {jl = ₃₆} {₂₆} {()}
  lemma-[12] {jl = ₃₆} {₃₆} {()}
  lemma-[12] {jl = ₃₆} {₄₆} {₃₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₃₆} {₅₆} {₃₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₃₇} {₀₇} {()}
  lemma-[12] {jl = ₃₇} {₁₇} {()}
  lemma-[12] {jl = ₃₇} {₂₇} {()}
  lemma-[12] {jl = ₃₇} {₃₇} {()}
  lemma-[12] {jl = ₃₇} {₄₇} {₃₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₃₇} {₅₇} {₃₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₃₇} {₆₇} {₃₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₄₅} {₀₅} {()}
  lemma-[12] {jl = ₄₅} {₁₅} {()}
  lemma-[12] {jl = ₄₅} {₂₅} {()}
  lemma-[12] {jl = ₄₅} {₃₅} {()}
  lemma-[12] {jl = ₄₅} {₄₅} {()}
  lemma-[12] {jl = ₄₆} {₀₆} {()}
  lemma-[12] {jl = ₄₆} {₁₆} {()}
  lemma-[12] {jl = ₄₆} {₂₆} {()}
  lemma-[12] {jl = ₄₆} {₃₆} {()}
  lemma-[12] {jl = ₄₆} {₄₆} {()}
  lemma-[12] {jl = ₄₆} {₅₆} {₄₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₄₇} {₀₇} {()}
  lemma-[12] {jl = ₄₇} {₁₇} {()}
  lemma-[12] {jl = ₄₇} {₂₇} {()}
  lemma-[12] {jl = ₄₇} {₃₇} {()}
  lemma-[12] {jl = ₄₇} {₄₇} {()}
  lemma-[12] {jl = ₄₇} {₅₇} {₄₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₄₇} {₆₇} {₄₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₅₆} {₀₆} {()}
  lemma-[12] {jl = ₅₆} {₁₆} {()}
  lemma-[12] {jl = ₅₆} {₂₆} {()}
  lemma-[12] {jl = ₅₆} {₃₆} {()}
  lemma-[12] {jl = ₅₆} {₄₆} {()}
  lemma-[12] {jl = ₅₆} {₅₆} {()}
  lemma-[12] {jl = ₅₇} {₀₇} {()}
  lemma-[12] {jl = ₅₇} {₁₇} {()}
  lemma-[12] {jl = ₅₇} {₂₇} {()}
  lemma-[12] {jl = ₅₇} {₃₇} {()}
  lemma-[12] {jl = ₅₇} {₄₇} {()}
  lemma-[12] {jl = ₅₇} {₅₇} {()}
  lemma-[12] {jl = ₅₇} {₆₇} {₅₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[12] {jl = ₆₇} {₀₇} {()}
  lemma-[12] {jl = ₆₇} {₁₇} {()}
  lemma-[12] {jl = ₆₇} {₂₇} {()}
  lemma-[12] {jl = ₆₇} {₃₇} {()}
  lemma-[12] {jl = ₆₇} {₄₇} {()}
  lemma-[12] {jl = ₆₇} {₅₇} {()}
  lemma-[12] {jl = ₆₇} {₆₇} {()}
