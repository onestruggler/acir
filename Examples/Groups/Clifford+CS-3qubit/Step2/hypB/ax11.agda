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

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax11 where

  lemma-[11] : ∀ {j k l} {kl : Less k l} -> {jk : Less j k} -> {jl : Less j l} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (X kl • X jk) === (g ʷ) (X jk • X jl)
  lemma-[11] {kl = ₀₁} {()} {jl}
  lemma-[11] {kl = ₀₂} {()} {jl}
  lemma-[11] {kl = ₀₃} {()} {jl}
  lemma-[11] {kl = ₀₄} {()} {jl}
  lemma-[11] {kl = ₀₅} {()} {jl}
  lemma-[11] {kl = ₀₆} {()} {jl}
  lemma-[11] {kl = ₀₇} {()} {jl}
  lemma-[11] {kl = ₁₂} {₀₁} {₀₂} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₁₃} {₀₁} {₀₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₁₄} {₀₁} {₀₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₁₅} {₀₁} {₀₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₁₆} {₀₁} {₀₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₁₇} {₀₁} {₀₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₃} {₀₂} {₀₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₃} {₁₂} {₁₃} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₄} {₀₂} {₀₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₄} {₁₂} {₁₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₅} {₀₂} {₀₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₅} {₁₂} {₁₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₆} {₀₂} {₀₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₆} {₁₂} {₁₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₇} {₀₂} {₀₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₂₇} {₁₂} {₁₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₄} {₀₃} {₀₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₄} {₁₃} {₁₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₄} {₂₃} {₂₄} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₅} {₀₃} {₀₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₅} {₁₃} {₁₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₅} {₂₃} {₂₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₆} {₀₃} {₀₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₆} {₁₃} {₁₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₆} {₂₃} {₂₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₇} {₀₃} {₀₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₇} {₁₃} {₁₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₃₇} {₂₃} {₂₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₅} {₀₄} {₀₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₅} {₁₄} {₁₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₅} {₂₄} {₂₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₅} {₃₄} {₃₅} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₆} {₀₄} {₀₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₆} {₁₄} {₁₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₆} {₂₄} {₂₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₆} {₃₄} {₃₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₇} {₀₄} {₀₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₇} {₁₄} {₁₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₇} {₂₄} {₂₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₄₇} {₃₄} {₃₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₆} {₀₅} {₀₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₆} {₁₅} {₁₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₆} {₂₅} {₂₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₆} {₃₅} {₃₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₆} {₄₅} {₄₆} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₇} {₀₅} {₀₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₇} {₁₅} {₁₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₇} {₂₅} {₂₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₇} {₃₅} {₃₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₅₇} {₄₅} {₄₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₆₇} {₀₆} {₀₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₆₇} {₁₆} {₁₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₆₇} {₂₆} {₂₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₆₇} {₃₆} {₃₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₆₇} {₄₆} {₄₇} = ListNF.listnfeq' nf-us8e auto
  lemma-[11] {kl = ₆₇} {₅₆} {₅₇} = ListNF.listnfeq' nf-us8e auto
