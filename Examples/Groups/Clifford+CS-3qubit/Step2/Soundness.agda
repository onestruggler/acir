------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open import Examples.Groups.Clifford+CS-3qubit.Index

open import Examples.Groups.Clifford+CS-3qubit.Step1.Theorem using (module TwoLevel-Less)
open TwoLevel-Less
open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified ; f)
open TwoLevel-Simplified

open import Examples.Groups.Clifford+CS-3qubit.Step2.TwoLevel-Less-Lemmas
open TwoLevel-Less-Rewrite
module TLR2 = TwoLevel-Less-Rewrite2
module TLR3 = TwoLevel-Less-Rewrite3

module Examples.Groups.Clifford+CS-3qubit.Step2.Soundness where

  soundness-base : ∀ {w v} -> w === v ∈ TwoLevel-Simplified.Rel -> TwoLevel-Less.Rel ⊢ (f ʷ) w === (f ʷ) v
  soundness-base [S1] = rewrite-twolevel 100 auto
  soundness-base [S3a] = rewrite-twolevel 100 auto
  soundness-base [S3b] = rewrite-twolevel 100 auto
  soundness-base [S3c] = rewrite-twolevel 100 auto
  soundness-base [S3d] = rewrite-twolevel 100 auto
  soundness-base [S3e] = rewrite-twolevel 100 auto
  soundness-base [S3f] = rewrite-twolevel 100 auto
  soundness-base [S3g] = rewrite-twolevel 100 auto
  soundness-base [S4a] = rewrite-twolevel 100 auto
  soundness-base [S4b] = rewrite-twolevel 100 auto
  soundness-base [S5a] = rewrite-twolevel 100 auto
  soundness-base [S5b] = rewrite-twolevel 100 auto
  soundness-base [S5c] = rewrite-twolevel 100 auto
  soundness-base [S5d] = rewrite-twolevel 100 auto
  soundness-base [S5e] = rewrite-twolevel 100 auto
  soundness-base [S5f] = rewrite-twolevel 100 auto
  soundness-base [S6] = rewrite-twolevel 100 auto
  soundness-base [S7a] = rewrite-twolevel 100 auto
  soundness-base [S7b] = rewrite-twolevel 100 auto
  soundness-base [S7c] = rewrite-twolevel 100 auto
  soundness-base [S7d] = rewrite-twolevel 100 auto
  soundness-base [S7e] = rewrite-twolevel 100 auto
  soundness-base [S8a] = rewrite-twolevel 100 auto
  soundness-base [S8b] = rewrite-twolevel 100 auto
  soundness-base [S8c] = rewrite-twolevel 100 auto
  soundness-base [S8d] = rewrite-twolevel 100 auto
  soundness-base [S8e] = rewrite-twolevel 100 auto
  soundness-base [S8f] = rewrite-twolevel 100 auto
  soundness-base [S8g] = rewrite-twolevel 100 auto
  soundness-base [S8h] = rewrite-twolevel 100 auto
  soundness-base [S8i] = rewrite-twolevel 100 auto
  soundness-base [S8j] = rewrite-twolevel 100 auto
  soundness-base [S8k] = rewrite-twolevel 100 auto
  soundness-base [S8l] = rewrite-twolevel 100 auto
  soundness-base [S8m] = rewrite-twolevel 100 auto
  soundness-base [S8n] = rewrite-twolevel 100 auto
  soundness-base [S8o] = rewrite-twolevel 100 auto
  soundness-base [S9a] = TLR2.rewrite-twolevel 100 auto 
  soundness-base [S9b] = TLR2.rewrite-twolevel 100 auto
  soundness-base [S9c] = TLR2.rewrite-twolevel 100 auto
  soundness-base [S9d] = TLR2.rewrite-twolevel 100 auto
  soundness-base [S9e] = TLR2.rewrite-twolevel 100 auto
  soundness-base [S9f] = TLR2.rewrite-twolevel 100 auto
  soundness-base [S10] = rewrite-twolevel 100 auto
  soundness-base [S11] = rewrite-twolevel 100 auto
  soundness-base [S12] = rewrite-twolevel 100 auto
  soundness-base [S14] = rewrite-twolevel 100 auto
  soundness-base [S15] =
    equational (f ʷ) (K₀₂ • K₁₃ • K₀₁ • K₂₃)
      by (TLR3.rewrite-twolevel 100 auto)
    equals (K ₀₂ • K ₁₃ • K ₀₁ • K ₂₃)
      by symm (axiom ([19a] {jk = ₀₁} {lm = ₂₃} {jl = ₀₂} {km = ₁₃} {kl = ₁₂}))
    equals (K ₀₁ • K ₂₃ • K ₀₂ • K ₁₃)
      by (TLR3.rewrite-twolevel 100 auto)
    equals (f ʷ) (K₀₁ • K₂₃ • K₀₂ • K₁₃)
      where
        open Monoid-Equational

  -- Proof of the soundness theorem: All the work was done in the base
  -- cases. The rest is just an obvious induction.
  soundness : ∀ {w v} -> TwoLevel-Simplified.Rel ⊢ w === v -> TwoLevel-Less.Rel ⊢ (f ʷ) w === (f ʷ) v
  soundness (axiom x) = soundness-base x
  soundness refl = refl
  soundness (symm deriv) = symm (soundness deriv)
  soundness (trans deriv deriv₁) = trans (soundness deriv) (soundness deriv₁)
  soundness (cong deriv deriv₁) = cong (soundness deriv) (soundness deriv₁)
  soundness assoc = assoc
  soundness left-unit = left-unit
  soundness right-unit = right-unit
