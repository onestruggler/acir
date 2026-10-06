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
open import Presentation.Tactics.Words

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)
open TwoLevel-Less
open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified ; f ; g)
open TwoLevel-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Simplified-Lemmas
open import Examples.Groups.Clifford+CS-3qubit.Step2.Lafont-S8

open Basis-Change group-like (Rewriting.step-cong TwoLevel-Simplified-Step.X-step)

module Examples.Groups.Clifford+CS-3qubit.Step2.hypB.ax5 where

  lemma-[5a] : ∀ {j k l} {kl : Less k l} -> {jk : Less j k} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j • X kl) === (g ʷ) (X kl • i j)

  lemma-[5a] {kl = ₀₁} {()}
  lemma-[5a] {kl = ₀₂} {()}
  lemma-[5a] {kl = ₀₃} {()}
  lemma-[5a] {kl = ₀₄} {()}
  lemma-[5a] {kl = ₀₅} {()}
  lemma-[5a] {kl = ₀₆} {()}
  lemma-[5a] {kl = ₀₇} {()}
  lemma-[5a] {kl = ₁₂} {₀₁} = axiom [S5a]
  lemma-[5a] {kl = ₁₃} {₀₁} = BC.by-basis-change (X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₁₄} {₀₁} = BC.by-basis-change (X₂₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₁₅} {₀₁} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₁₆} {₀₁} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₁₇} {₀₁} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₃} {₀₂} = BC.by-basis-change (X₂₃ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₃} {₁₂} = BC.by-basis-change (X₂₃ • X₁₂ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₄} {₀₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₄} {₁₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₅} {₀₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₅} {₁₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₆} {₀₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₆} {₁₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₇} {₀₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₂₇} {₁₂} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₄} {₀₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₄} {₁₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₄} {₂₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₅} {₀₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₅} {₁₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₀₁ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₅} {₂₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₆} {₀₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₆} {₁₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₀₁ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₆} {₂₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₇} {₀₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₇} {₁₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₀₁ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₃₇} {₂₃} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₀₁ • X₂₃ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₅} {₀₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₅} {₁₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₅} {₂₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₅} {₃₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₆} {₀₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₆} {₁₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₆} {₂₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₆} {₃₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₇} {₀₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₇} {₁₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₇} {₂₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₄₇} {₃₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₆} {₀₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₆} {₁₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₆} {₂₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₆} {₃₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₆} {₄₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₇} {₀₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₇} {₁₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₇} {₂₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₇} {₃₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₅₇} {₄₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₀₁ • X₁₂ • X₂₃ • X₄₅ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₆₇} {₀₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₆₇} {₁₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₆₇} {₂₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₆₇} {₃₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₆₇} {₄₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5a] {kl = ₆₇} {₅₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto

  lemma-[5b] : ∀ {j k l} {kl : Less k l} -> {lj : Less l j} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j • X kl) === (g ʷ) (X kl • i j)

  lemma-[5b] {.₂} {.₀} {.₁} {₀₁} {₁₂} = BC.by-basis-change (X₀₁ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₃} {.₀} {.₁} {₀₁} {₁₃} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₄} {.₀} {.₁} {₀₁} {₁₄} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₅} {.₀} {.₁} {₀₁} {₁₅} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₀} {.₁} {₀₁} {₁₆} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₀} {.₁} {₀₁} {₁₇} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₃} {.₀} {.₂} {₀₂} {₂₃} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₄} {.₀} {.₂} {₀₂} {₂₄} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₅} {.₀} {.₂} {₀₂} {₂₅} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₀} {.₂} {₀₂} {₂₆} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₀} {.₂} {₀₂} {₂₇} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₄} {.₀} {.₃} {₀₃} {₃₄} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₅} {.₀} {.₃} {₀₃} {₃₅} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₀} {.₃} {₀₃} {₃₆} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₀} {.₃} {₀₃} {₃₇} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₅} {.₀} {.₄} {₀₄} {₄₅} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₀} {.₄} {₀₄} {₄₆} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₀} {.₄} {₀₄} {₄₇} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₀} {.₅} {₀₅} {₅₆} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₀} {.₅} {₀₅} {₅₇} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₀} {.₆} {₀₆} {₆₇} = BC.by-basis-change (X₀₁ • X₁₂ • X₂₃ • X₁₂ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {j} {.₀} {.₇} {₀₇} {()}
  lemma-[5b] {.₃} {.₁} {.₂} {₁₂} {₂₃} = BC.by-basis-change (X₀₃) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₄} {.₁} {.₂} {₁₂} {₂₄} = BC.by-basis-change (X₀₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₅} {.₁} {.₂} {₁₂} {₂₅} = BC.by-basis-change (X₀₃ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₁} {.₂} {₁₂} {₂₆} = BC.by-basis-change (X₀₃ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₁} {.₂} {₁₂} {₂₇} = BC.by-basis-change (X₀₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₄} {.₁} {.₃} {₁₃} {₃₄} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₅} {.₁} {.₃} {₁₃} {₃₅} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₁} {.₃} {₁₃} {₃₆} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₁} {.₃} {₁₃} {₃₇} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₅} {.₁} {.₄} {₁₄} {₄₅} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₁} {.₄} {₁₄} {₄₆} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₁} {.₄} {₁₄} {₄₇} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₆} {.₁} {.₅} {₁₅} {₅₆} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₁} {.₅} {₁₅} {₅₇} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5b] {.₇} {.₁} {.₆} {₁₆} {₆₇} = BC.by-basis-change (X₀₃ • X₃₄ • X₂₃ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5b] {j} {.₁} {.₇} {₁₇} {()}
  lemma-[5b] {.₄} {.₂} {.₃} {₂₃} {₃₄} = BC.by-basis-change (X₀₄) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₅} {.₂} {.₃} {₂₃} {₃₅} = BC.by-basis-change (X₀₄ • X₄₅) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₆} {.₂} {.₃} {₂₃} {₃₆} = BC.by-basis-change (X₀₄ • X₄₅ • X₅₆) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₇} {.₂} {.₃} {₂₃} {₃₇} = BC.by-basis-change (X₀₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₅} {.₂} {.₄} {₂₄} {₄₅} = BC.by-basis-change (X₀₄ • X₄₅ • X₃₄) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₆} {.₂} {.₄} {₂₄} {₄₆} = BC.by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₇} {.₂} {.₄} {₂₄} {₄₇} = BC.by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₆₇) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₆} {.₂} {.₅} {₂₅} {₅₆} = BC.by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₄₅) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₇} {.₂} {.₅} {₂₅} {₅₇} = BC.by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇) ((axiom [S5b])) 200 auto
  lemma-[5b] {.₇} {.₂} {.₆} {₂₆} {₆₇} = BC.by-basis-change (X₀₄ • X₄₅ • X₃₄ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((axiom [S5b])) 200 auto
  lemma-[5b] {j} {.₂} {.₇} {₂₇} {()}
  lemma-[5b] {.₅} {.₃} {.₄} {₃₄} {₄₅} = BC.by-basis-change (X₀₅) ((axiom [S5c])) 200 auto
  lemma-[5b] {.₆} {.₃} {.₄} {₃₄} {₄₆} = BC.by-basis-change (X₀₅ • X₅₆) ((axiom [S5c])) 200 auto
  lemma-[5b] {.₇} {.₃} {.₄} {₃₄} {₄₇} = BC.by-basis-change (X₀₅ • X₅₆ • X₆₇) ((axiom [S5c])) 200 auto
  lemma-[5b] {.₆} {.₃} {.₅} {₃₅} {₅₆} = BC.by-basis-change (X₀₅ • X₅₆ • X₄₅) ((axiom [S5c])) 200 auto
  lemma-[5b] {.₇} {.₃} {.₅} {₃₅} {₅₇} = BC.by-basis-change (X₀₅ • X₅₆ • X₄₅ • X₆₇) ((axiom [S5c])) 200 auto
  lemma-[5b] {.₇} {.₃} {.₆} {₃₆} {₆₇} = BC.by-basis-change (X₀₅ • X₅₆ • X₄₅ • X₆₇ • X₅₆) ((axiom [S5c])) 200 auto
  lemma-[5b] {j} {.₃} {.₇} {₃₇} {()}
  lemma-[5b] {.₆} {.₄} {.₅} {₄₅} {₅₆} = BC.by-basis-change (X₀₆) ((axiom [S5d])) 200 auto
  lemma-[5b] {.₇} {.₄} {.₅} {₄₅} {₅₇} = BC.by-basis-change (X₀₆ • X₆₇) ((axiom [S5d])) 200 auto
  lemma-[5b] {.₇} {.₄} {.₆} {₄₆} {₆₇} = BC.by-basis-change (X₀₆ • X₆₇ • X₅₆) ((axiom [S5d])) 200 auto
  lemma-[5b] {j} {.₄} {.₇} {₄₇} {()}
  lemma-[5b] {.₇} {.₅} {.₆} {₅₆} {₆₇} = BC.by-basis-change (X₀₇) ((axiom [S5e])) 200 auto
  lemma-[5b] {j} {.₅} {.₇} {₅₇} {()}
  lemma-[5b] {j} {.₆} {.₇} {₆₇} {()}



  lemma-[5c] : ∀ {j k l} {kl : Less k l} -> {kj : Less k j} -> {jl : Less j l} -> TwoLevel-Simplified.Rel ⊢ (g ʷ) (i j • X kl) === (g ʷ) (X kl • i j)
  lemma-[5c] {₀} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₀} {₁} {₀₁} {()} {jl}
  lemma-[5c] {₀} {₀} {₂} {₀₂} {()} {jl}
  lemma-[5c] {₀} {₀} {₃} {₀₃} {()} {jl}
  lemma-[5c] {₀} {₀} {₄} {₀₄} {()} {jl}
  lemma-[5c] {₀} {₀} {₅} {₀₅} {()} {jl}
  lemma-[5c] {₀} {₀} {₆} {₀₆} {()} {jl}
  lemma-[5c] {₀} {₀} {₇} {₀₇} {()} {jl}
  lemma-[5c] {₀} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₀} {₁} {₂} {₁₂} {()} {jl}
  lemma-[5c] {₀} {₁} {₃} {₁₃} {()} {jl}
  lemma-[5c] {₀} {₁} {₄} {₁₄} {()} {jl}
  lemma-[5c] {₀} {₁} {₅} {₁₅} {()} {jl}
  lemma-[5c] {₀} {₁} {₆} {₁₆} {()} {jl}
  lemma-[5c] {₀} {₁} {₇} {₁₇} {()} {jl}
  lemma-[5c] {₀} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₀} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₀} {₂} {₃} {₂₃} {()} {jl}
  lemma-[5c] {₀} {₂} {₄} {₂₄} {()} {jl}
  lemma-[5c] {₀} {₂} {₅} {₂₅} {()} {jl}
  lemma-[5c] {₀} {₂} {₆} {₂₆} {()} {jl}
  lemma-[5c] {₀} {₂} {₇} {₂₇} {()} {jl}
  lemma-[5c] {₀} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₀} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₀} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₀} {₃} {₄} {₃₄} {()} {jl}
  lemma-[5c] {₀} {₃} {₅} {₃₅} {()} {jl}
  lemma-[5c] {₀} {₃} {₆} {₃₆} {()} {jl}
  lemma-[5c] {₀} {₃} {₇} {₃₇} {()} {jl}
  lemma-[5c] {₀} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₀} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₀} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₀} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₀} {₄} {₅} {₄₅} {()} {jl}
  lemma-[5c] {₀} {₄} {₆} {₄₆} {()} {jl}
  lemma-[5c] {₀} {₄} {₇} {₄₇} {()} {jl}
  lemma-[5c] {₀} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₀} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₀} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₀} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₀} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₀} {₅} {₆} {₅₆} {()} {jl}
  lemma-[5c] {₀} {₅} {₇} {₅₇} {()} {jl}
  lemma-[5c] {₀} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₀} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₀} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₀} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₀} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₀} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₀} {₆} {₇} {₆₇} {()} {jl}
  lemma-[5c] {₀} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₀} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₀} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₀} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₀} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₀} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₀} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₀} {₇} {₇} {()} {kj} {jl}
  lemma-[5c] {₁} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₀} {₁} {₀₁} {₀₁} {()}
  lemma-[5c] {₁} {₀} {₂} {₀₂} {₀₁} {₁₂} = BC.by-basis-change (X₀₁) ((axiom [S5a])) 200 auto
  lemma-[5c] {₁} {₀} {₃} {₀₃} {₀₁} {₁₃} = BC.by-basis-change (X₀₁ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5c] {₁} {₀} {₄} {₀₄} {₀₁} {₁₄} = BC.by-basis-change (X₀₁ • X₂₃ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5c] {₁} {₀} {₅} {₀₅} {₀₁} {₁₅} = BC.by-basis-change (X₀₁ • X₂₃ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5c] {₁} {₀} {₆} {₀₆} {₀₁} {₁₆} = BC.by-basis-change (X₀₁ • X₂₃ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5c] {₁} {₀} {₇} {₀₇} {₀₁} {₁₇} = BC.by-basis-change (X₀₁ • X₂₃ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5c] {₁} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₁} {₁} {₂} {₁₂} {()} {jl}
  lemma-[5c] {₁} {₁} {₃} {₁₃} {()} {jl}
  lemma-[5c] {₁} {₁} {₄} {₁₄} {()} {jl}
  lemma-[5c] {₁} {₁} {₅} {₁₅} {()} {jl}
  lemma-[5c] {₁} {₁} {₆} {₁₆} {()} {jl}
  lemma-[5c] {₁} {₁} {₇} {₁₇} {()} {jl}
  lemma-[5c] {₁} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₁} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₁} {₂} {₃} {₂₃} {()} {jl}
  lemma-[5c] {₁} {₂} {₄} {₂₄} {()} {jl}
  lemma-[5c] {₁} {₂} {₅} {₂₅} {()} {jl}
  lemma-[5c] {₁} {₂} {₆} {₂₆} {()} {jl}
  lemma-[5c] {₁} {₂} {₇} {₂₇} {()} {jl}
  lemma-[5c] {₁} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₁} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₁} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₁} {₃} {₄} {₃₄} {()} {jl}
  lemma-[5c] {₁} {₃} {₅} {₃₅} {()} {jl}
  lemma-[5c] {₁} {₃} {₆} {₃₆} {()} {jl}
  lemma-[5c] {₁} {₃} {₇} {₃₇} {()} {jl}
  lemma-[5c] {₁} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₁} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₁} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₁} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₁} {₄} {₅} {₄₅} {()} {jl}
  lemma-[5c] {₁} {₄} {₆} {₄₆} {()} {jl}
  lemma-[5c] {₁} {₄} {₇} {₄₇} {()} {jl}
  lemma-[5c] {₁} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₁} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₁} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₁} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₁} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₁} {₅} {₆} {₅₆} {()} {jl}
  lemma-[5c] {₁} {₅} {₇} {₅₇} {()} {jl}
  lemma-[5c] {₁} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₁} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₁} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₁} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₁} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₁} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₁} {₆} {₇} {₆₇} {()} {jl}
  lemma-[5c] {₁} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₁} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₁} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₁} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₁} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₁} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₁} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₁} {₇} {₇} {()} {kj} {jl}
  lemma-[5c] {₂} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₀} {₁} {₀₁} {₀₂} {()}
  lemma-[5c] {₂} {₀} {₂} {₀₂} {₀₂} {()}
  lemma-[5c] {₂} {₀} {₃} {₀₃} {₀₂} {₂₃} = BC.by-basis-change (X₀₁ • X₂₃ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₀} {₄} {₀₄} {₀₂} {₂₄} = BC.by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₀} {₅} {₀₅} {₀₂} {₂₅} = BC.by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₀} {₆} {₀₆} {₀₂} {₂₆} = BC.by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₀} {₇} {₀₇} {₀₂} {₂₇} = BC.by-basis-change (X₀₁ • X₂₃ • X₁₂ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₂} {₁} {₂} {₁₂} {₁₂} {()}
  lemma-[5c] {₂} {₁} {₃} {₁₃} {₁₂} {₂₃} = BC.by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₁} {₄} {₁₄} {₁₂} {₂₄} = BC.by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₁} {₅} {₁₅} {₁₂} {₂₅} = BC.by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₁} {₆} {₁₆} {₁₂} {₂₆} = BC.by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₁} {₇} {₁₇} {₁₂} {₂₇} = BC.by-basis-change (X₂₃ • X₁₂ • X₀₁ • X₁₂ • X₃₄ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5c] {₂} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₂} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₂} {₂} {₃} {₂₃} {()} {jl}
  lemma-[5c] {₂} {₂} {₄} {₂₄} {()} {jl}
  lemma-[5c] {₂} {₂} {₅} {₂₅} {()} {jl}
  lemma-[5c] {₂} {₂} {₆} {₂₆} {()} {jl}
  lemma-[5c] {₂} {₂} {₇} {₂₇} {()} {jl}
  lemma-[5c] {₂} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₂} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₂} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₂} {₃} {₄} {₃₄} {()} {jl}
  lemma-[5c] {₂} {₃} {₅} {₃₅} {()} {jl}
  lemma-[5c] {₂} {₃} {₆} {₃₆} {()} {jl}
  lemma-[5c] {₂} {₃} {₇} {₃₇} {()} {jl}
  lemma-[5c] {₂} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₂} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₂} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₂} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₂} {₄} {₅} {₄₅} {()} {jl}
  lemma-[5c] {₂} {₄} {₆} {₄₆} {()} {jl}
  lemma-[5c] {₂} {₄} {₇} {₄₇} {()} {jl}
  lemma-[5c] {₂} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₂} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₂} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₂} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₂} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₂} {₅} {₆} {₅₆} {()} {jl}
  lemma-[5c] {₂} {₅} {₇} {₅₇} {()} {jl}
  lemma-[5c] {₂} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₂} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₂} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₂} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₂} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₂} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₂} {₆} {₇} {₆₇} {()} {jl}
  lemma-[5c] {₂} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₂} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₂} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₂} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₂} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₂} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₂} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₂} {₇} {₇} {()} {kj} {jl}
  lemma-[5c] {₃} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₀} {₁} {₀₁} {₀₃} {()}
  lemma-[5c] {₃} {₀} {₂} {₀₂} {₀₃} {()}
  lemma-[5c] {₃} {₀} {₃} {₀₃} {₀₃} {()}
  lemma-[5c] {₃} {₀} {₄} {₀₄} {₀₃} {₃₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₀} {₅} {₀₅} {₀₃} {₃₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₀} {₆} {₀₆} {₀₃} {₃₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₀} {₇} {₀₇} {₀₃} {₃₇} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₂₃ • X₀₃ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₃} {₁} {₂} {₁₂} {₁₃} {()}
  lemma-[5c] {₃} {₁} {₃} {₁₃} {₁₃} {()}
  lemma-[5c] {₃} {₁} {₄} {₁₄} {₁₃} {₃₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₁} {₅} {₁₅} {₁₃} {₃₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₁} {₆} {₁₆} {₁₃} {₃₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₁} {₇} {₁₇} {₁₃} {₃₇} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₃ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₃} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₃} {₂} {₃} {₂₃} {₂₃} {()}
  lemma-[5c] {₃} {₂} {₄} {₂₄} {₂₃} {₃₄} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₂} {₅} {₂₅} {₂₃} {₃₅} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃ • X₄₅) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₂} {₆} {₂₆} {₂₃} {₃₆} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃ • X₄₅ • X₅₆) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₂} {₇} {₂₇} {₂₃} {₃₇} = BC.by-basis-change (X₂₃ • X₃₄ • X₁₂ • X₀₁ • X₂₃ • X₁₂ • X₂₃ • X₄₅ • X₅₆ • X₆₇) ((axiom [S5a])) 200 auto
  lemma-[5c] {₃} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₃} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₃} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₃} {₃} {₄} {₃₄} {()} {jl}
  lemma-[5c] {₃} {₃} {₅} {₃₅} {()} {jl}
  lemma-[5c] {₃} {₃} {₆} {₃₆} {()} {jl}
  lemma-[5c] {₃} {₃} {₇} {₃₇} {()} {jl}
  lemma-[5c] {₃} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₃} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₃} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₃} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₃} {₄} {₅} {₄₅} {()} {jl}
  lemma-[5c] {₃} {₄} {₆} {₄₆} {()} {jl}
  lemma-[5c] {₃} {₄} {₇} {₄₇} {()} {jl}
  lemma-[5c] {₃} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₃} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₃} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₃} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₃} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₃} {₅} {₆} {₅₆} {()} {jl}
  lemma-[5c] {₃} {₅} {₇} {₅₇} {()} {jl}
  lemma-[5c] {₃} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₃} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₃} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₃} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₃} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₃} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₃} {₆} {₇} {₆₇} {()} {jl}
  lemma-[5c] {₃} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₃} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₃} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₃} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₃} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₃} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₃} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₃} {₇} {₇} {()} {kj} {jl}
  lemma-[5c] {₄} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₀} {₁} {₀₁} {₀₄} {()}
  lemma-[5c] {₄} {₀} {₂} {₀₂} {₀₄} {()}
  lemma-[5c] {₄} {₀} {₃} {₀₃} {₀₄} {()}
  lemma-[5c] {₄} {₀} {₄} {₀₄} {₀₄} {()}
  lemma-[5c] {₄} {₀} {₅} {₀₅} {₀₄} {₄₅} = BC.by-basis-change (X₀₄) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₀} {₆} {₀₆} {₀₄} {₄₆} = BC.by-basis-change (X₀₄ • X₅₆) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₀} {₇} {₀₇} {₀₄} {₄₇} = BC.by-basis-change (X₀₄ • X₅₆ • X₆₇) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₄} {₁} {₂} {₁₂} {₁₄} {()}
  lemma-[5c] {₄} {₁} {₃} {₁₃} {₁₄} {()}
  lemma-[5c] {₄} {₁} {₄} {₁₄} {₁₄} {()}
  lemma-[5c] {₄} {₁} {₅} {₁₅} {₁₄} {₄₅} = BC.by-basis-change (X₀₄ • X₀₁) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₁} {₆} {₁₆} {₁₄} {₄₆} = BC.by-basis-change (X₀₄ • X₀₁ • X₅₆) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₁} {₇} {₁₇} {₁₄} {₄₇} = BC.by-basis-change (X₀₄ • X₀₁ • X₅₆ • X₆₇) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₄} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₄} {₂} {₃} {₂₃} {₂₄} {()}
  lemma-[5c] {₄} {₂} {₄} {₂₄} {₂₄} {()}
  lemma-[5c] {₄} {₂} {₅} {₂₅} {₂₄} {₄₅} = BC.by-basis-change (X₀₄ • X₀₁ • X₁₂) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₂} {₆} {₂₆} {₂₄} {₄₆} = BC.by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₅₆) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₂} {₇} {₂₇} {₂₄} {₄₇} = BC.by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₅₆ • X₆₇) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₄} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₄} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₄} {₃} {₄} {₃₄} {₃₄} {()}
  lemma-[5c] {₄} {₃} {₅} {₃₅} {₃₄} {₄₅} = BC.by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₂₃) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₃} {₆} {₃₆} {₃₄} {₄₆} = BC.by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₂₃ • X₅₆) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₃} {₇} {₃₇} {₃₄} {₄₇} = BC.by-basis-change (X₀₄ • X₀₁ • X₁₂ • X₂₃ • X₅₆ • X₆₇) ((axiom [S5d])) 200 auto
  lemma-[5c] {₄} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₄} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₄} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₄} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₄} {₄} {₅} {₄₅} {()} {jl}
  lemma-[5c] {₄} {₄} {₆} {₄₆} {()} {jl}
  lemma-[5c] {₄} {₄} {₇} {₄₇} {()} {jl}
  lemma-[5c] {₄} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₄} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₄} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₄} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₄} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₄} {₅} {₆} {₅₆} {()} {jl}
  lemma-[5c] {₄} {₅} {₇} {₅₇} {()} {jl}
  lemma-[5c] {₄} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₄} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₄} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₄} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₄} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₄} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₄} {₆} {₇} {₆₇} {()} {jl}
  lemma-[5c] {₄} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₄} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₄} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₄} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₄} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₄} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₄} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₄} {₇} {₇} {()} {kj} {jl}
  lemma-[5c] {₅} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₀} {₁} {₀₁} {₀₅} {()}
  lemma-[5c] {₅} {₀} {₂} {₀₂} {₀₅} {()}
  lemma-[5c] {₅} {₀} {₃} {₀₃} {₀₅} {()}
  lemma-[5c] {₅} {₀} {₄} {₀₄} {₀₅} {()}
  lemma-[5c] {₅} {₀} {₅} {₀₅} {₀₅} {()}
  lemma-[5c] {₅} {₀} {₆} {₀₆} {₀₅} {₅₆} = BC.by-basis-change (X₀₅) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₀} {₇} {₀₇} {₀₅} {₅₇} = BC.by-basis-change (X₀₅ • X₆₇) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₅} {₁} {₂} {₁₂} {₁₅} {()}
  lemma-[5c] {₅} {₁} {₃} {₁₃} {₁₅} {()}
  lemma-[5c] {₅} {₁} {₄} {₁₄} {₁₅} {()}
  lemma-[5c] {₅} {₁} {₅} {₁₅} {₁₅} {()}
  lemma-[5c] {₅} {₁} {₆} {₁₆} {₁₅} {₅₆} = BC.by-basis-change (X₀₅ • X₀₁) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₁} {₇} {₁₇} {₁₅} {₅₇} = BC.by-basis-change (X₀₅ • X₀₁ • X₆₇) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₅} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₅} {₂} {₃} {₂₃} {₂₅} {()}
  lemma-[5c] {₅} {₂} {₄} {₂₄} {₂₅} {()}
  lemma-[5c] {₅} {₂} {₅} {₂₅} {₂₅} {()}
  lemma-[5c] {₅} {₂} {₆} {₂₆} {₂₅} {₅₆} = BC.by-basis-change (X₀₅ • X₀₁ • X₁₂) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₂} {₇} {₂₇} {₂₅} {₅₇} = BC.by-basis-change (X₀₅ • X₀₁ • X₁₂ • X₆₇) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₅} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₅} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₅} {₃} {₄} {₃₄} {₃₅} {()}
  lemma-[5c] {₅} {₃} {₅} {₃₅} {₃₅} {()}
  lemma-[5c] {₅} {₃} {₆} {₃₆} {₃₅} {₅₆} = BC.by-basis-change (X₀₅ • X₀₁ • X₁₂ • X₂₃) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₃} {₇} {₃₇} {₃₅} {₅₇} = BC.by-basis-change (X₀₅ • X₀₁ • X₁₂ • X₂₃ • X₆₇) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₅} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₅} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₅} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₅} {₄} {₅} {₄₅} {₄₅} {()}
  lemma-[5c] {₅} {₄} {₆} {₄₆} {₄₅} {₅₆} = BC.by-basis-change (X₀₄ • X₄₅) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₄} {₇} {₄₇} {₄₅} {₅₇} = BC.by-basis-change (X₀₄ • X₄₅ • X₆₇) ((axiom [S5e])) 200 auto
  lemma-[5c] {₅} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₅} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₅} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₅} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₅} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₅} {₅} {₆} {₅₆} {()} {jl}
  lemma-[5c] {₅} {₅} {₇} {₅₇} {()} {jl}
  lemma-[5c] {₅} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₅} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₅} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₅} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₅} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₅} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₅} {₆} {₇} {₆₇} {()} {jl}
  lemma-[5c] {₅} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₅} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₅} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₅} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₅} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₅} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₅} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₅} {₇} {₇} {()} {kj} {jl}
  lemma-[5c] {₆} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₀} {₁} {₀₁} {₀₆} {()}
  lemma-[5c] {₆} {₀} {₂} {₀₂} {₀₆} {()}
  lemma-[5c] {₆} {₀} {₃} {₀₃} {₀₆} {()}
  lemma-[5c] {₆} {₀} {₄} {₀₄} {₀₆} {()}
  lemma-[5c] {₆} {₀} {₅} {₀₅} {₀₆} {()}
  lemma-[5c] {₆} {₀} {₆} {₀₆} {₀₆} {()}
  lemma-[5c] {₆} {₀} {₇} {₀₇} {₀₆} {₆₇} = BC.by-basis-change (X₀₆) ((axiom [S5f])) 200 auto
  lemma-[5c] {₆} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₆} {₁} {₂} {₁₂} {₁₆} {()}
  lemma-[5c] {₆} {₁} {₃} {₁₃} {₁₆} {()}
  lemma-[5c] {₆} {₁} {₄} {₁₄} {₁₆} {()}
  lemma-[5c] {₆} {₁} {₅} {₁₅} {₁₆} {()}
  lemma-[5c] {₆} {₁} {₆} {₁₆} {₁₆} {()}
  lemma-[5c] {₆} {₁} {₇} {₁₇} {₁₆} {₆₇} = BC.by-basis-change (X₀₆ • X₀₁) ((axiom [S5f])) 200 auto
  lemma-[5c] {₆} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₆} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₆} {₂} {₃} {₂₃} {₂₆} {()}
  lemma-[5c] {₆} {₂} {₄} {₂₄} {₂₆} {()}
  lemma-[5c] {₆} {₂} {₅} {₂₅} {₂₆} {()}
  lemma-[5c] {₆} {₂} {₆} {₂₆} {₂₆} {()}
  lemma-[5c] {₆} {₂} {₇} {₂₇} {₂₆} {₆₇} = BC.by-basis-change (X₀₆ • X₀₁ • X₁₂) ((axiom [S5f])) 200 auto
  lemma-[5c] {₆} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₆} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₆} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₆} {₃} {₄} {₃₄} {₃₆} {()}
  lemma-[5c] {₆} {₃} {₅} {₃₅} {₃₆} {()}
  lemma-[5c] {₆} {₃} {₆} {₃₆} {₃₆} {()}
  lemma-[5c] {₆} {₃} {₇} {₃₇} {₃₆} {₆₇} = BC.by-basis-change (X₀₆ • X₀₁ • X₁₂ • X₂₃) ((axiom [S5f])) 200 auto
  lemma-[5c] {₆} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₆} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₆} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₆} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₆} {₄} {₅} {₄₅} {₄₆} {()}
  lemma-[5c] {₆} {₄} {₆} {₄₆} {₄₆} {()}
  lemma-[5c] {₆} {₄} {₇} {₄₇} {₄₆} {₆₇} = BC.by-basis-change (X₀₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄) ((axiom [S5f])) 200 auto
  lemma-[5c] {₆} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₆} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₆} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₆} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₆} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₆} {₅} {₆} {₅₆} {₅₆} {()}
  lemma-[5c] {₆} {₅} {₇} {₅₇} {₅₆} {₆₇} = BC.by-basis-change (X₀₆ • X₀₁ • X₁₂ • X₂₃ • X₃₄ • X₄₅) ((axiom [S5f])) 200 auto
  lemma-[5c] {₆} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₆} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₆} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₆} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₆} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₆} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₆} {₆} {₇} {₆₇} {()} {jl}
  lemma-[5c] {₆} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₆} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₆} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₆} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₆} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₆} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₆} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₆} {₇} {₇} {()} {kj} {jl}
  lemma-[5c] {₇} {₀} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₀} {₁} {₀₁} {₀₇} {()}
  lemma-[5c] {₇} {₀} {₂} {₀₂} {₀₇} {()}
  lemma-[5c] {₇} {₀} {₃} {₀₃} {₀₇} {()}
  lemma-[5c] {₇} {₀} {₄} {₀₄} {₀₇} {()}
  lemma-[5c] {₇} {₀} {₅} {₀₅} {₀₇} {()}
  lemma-[5c] {₇} {₀} {₆} {₀₆} {₀₇} {()}
  lemma-[5c] {₇} {₀} {₇} {₀₇} {₀₇} {()}
  lemma-[5c] {₇} {₁} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₁} {₁} {()} {kj} {jl}
  lemma-[5c] {₇} {₁} {₂} {₁₂} {₁₇} {()}
  lemma-[5c] {₇} {₁} {₃} {₁₃} {₁₇} {()}
  lemma-[5c] {₇} {₁} {₄} {₁₄} {₁₇} {()}
  lemma-[5c] {₇} {₁} {₅} {₁₅} {₁₇} {()}
  lemma-[5c] {₇} {₁} {₆} {₁₆} {₁₇} {()}
  lemma-[5c] {₇} {₁} {₇} {₁₇} {₁₇} {()}
  lemma-[5c] {₇} {₂} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₂} {₁} {()} {kj} {jl}
  lemma-[5c] {₇} {₂} {₂} {()} {kj} {jl}
  lemma-[5c] {₇} {₂} {₃} {₂₃} {₂₇} {()}
  lemma-[5c] {₇} {₂} {₄} {₂₄} {₂₇} {()}
  lemma-[5c] {₇} {₂} {₅} {₂₅} {₂₇} {()}
  lemma-[5c] {₇} {₂} {₆} {₂₆} {₂₇} {()}
  lemma-[5c] {₇} {₂} {₇} {₂₇} {₂₇} {()}
  lemma-[5c] {₇} {₃} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₃} {₁} {()} {kj} {jl}
  lemma-[5c] {₇} {₃} {₂} {()} {kj} {jl}
  lemma-[5c] {₇} {₃} {₃} {()} {kj} {jl}
  lemma-[5c] {₇} {₃} {₄} {₃₄} {₃₇} {()}
  lemma-[5c] {₇} {₃} {₅} {₃₅} {₃₇} {()}
  lemma-[5c] {₇} {₃} {₆} {₃₆} {₃₇} {()}
  lemma-[5c] {₇} {₃} {₇} {₃₇} {₃₇} {()}
  lemma-[5c] {₇} {₄} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₄} {₁} {()} {kj} {jl}
  lemma-[5c] {₇} {₄} {₂} {()} {kj} {jl}
  lemma-[5c] {₇} {₄} {₃} {()} {kj} {jl}
  lemma-[5c] {₇} {₄} {₄} {()} {kj} {jl}
  lemma-[5c] {₇} {₄} {₅} {₄₅} {₄₇} {()}
  lemma-[5c] {₇} {₄} {₆} {₄₆} {₄₇} {()}
  lemma-[5c] {₇} {₄} {₇} {₄₇} {₄₇} {()}
  lemma-[5c] {₇} {₅} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₅} {₁} {()} {kj} {jl}
  lemma-[5c] {₇} {₅} {₂} {()} {kj} {jl}
  lemma-[5c] {₇} {₅} {₃} {()} {kj} {jl}
  lemma-[5c] {₇} {₅} {₄} {()} {kj} {jl}
  lemma-[5c] {₇} {₅} {₅} {()} {kj} {jl}
  lemma-[5c] {₇} {₅} {₆} {₅₆} {₅₇} {()}
  lemma-[5c] {₇} {₅} {₇} {₅₇} {₅₇} {()}
  lemma-[5c] {₇} {₆} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₆} {₁} {()} {kj} {jl}
  lemma-[5c] {₇} {₆} {₂} {()} {kj} {jl}
  lemma-[5c] {₇} {₆} {₃} {()} {kj} {jl}
  lemma-[5c] {₇} {₆} {₄} {()} {kj} {jl}
  lemma-[5c] {₇} {₆} {₅} {()} {kj} {jl}
  lemma-[5c] {₇} {₆} {₆} {()} {kj} {jl}
  lemma-[5c] {₇} {₆} {₇} {₆₇} {₆₇} {()}
  lemma-[5c] {₇} {₇} {₀} {()} {kj} {jl}
  lemma-[5c] {₇} {₇} {₁} {()} {kj} {jl}
  lemma-[5c] {₇} {₇} {₂} {()} {kj} {jl}
  lemma-[5c] {₇} {₇} {₃} {()} {kj} {jl}
  lemma-[5c] {₇} {₇} {₄} {()} {kj} {jl}
  lemma-[5c] {₇} {₇} {₅} {()} {kj} {jl}
  lemma-[5c] {₇} {₇} {₆} {()} {kj} {jl}
  lemma-[5c] {₇} {₇} {₇} {()} {kj} {jl}
