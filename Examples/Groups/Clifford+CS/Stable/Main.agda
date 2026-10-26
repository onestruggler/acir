------------------------------------------------------------------------
-- Presentations of groups
--
-- The Clifford+CS circuits: a sound and complete rule set at every width
--
-- Stable.Theorem and Stable.Presentation with their two hypotheses
-- discharged: completeness on four wires (Four.Complete) and on five
-- (Five.Main, carried into the theory of Stable.Rules by `embed₅`).
-- Below five wires the rules of Syntactics are complete already
-- (Completeness, Four.Complete), and `embed` carries them in.  So the
-- theory of Stable.Rules — the rules of Syntactics, AX and the
-- controlled four-wire rules on five wires, and the control schema over
-- those — is sound (`soundᵧ`) and complete (`complete`) at every width,
-- and from four wires on it presents the circuits' unitaries
-- (`presentation`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Main where

open import Data.Nat using (suc)

open import Examples.Groups.Clifford+CS.Completeness
  using (complete₀ ; complete₁ ; complete₂ ; complete₃)
open import Examples.Groups.Clifford+CS.Four.Complete using (complete₄)
open import Examples.Groups.Clifford+CS.Five.Main using (complete₅)
open import Examples.Groups.Clifford+CS.Stable.Rules using (embed ; embed₅)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)
open import Examples.Groups.Clifford+CS.Stable.Soundness public using (soundᵧ)

------------------------------------------------------------------------
-- Completeness on five wires, in the theory of Stable.Rules

complete₅ᵧ : Completeᵧ 5
complete₅ᵧ e = embed₅ (complete₅ e)

import Examples.Groups.Clifford+CS.Stable.Theorem complete₄ complete₅ᵧ as Theorem
open import Examples.Groups.Clifford+CS.Stable.Presentation complete₄ complete₅ᵧ public
  using (presentation ; grouplikeᵧ)

------------------------------------------------------------------------
-- Completeness at every width

complete : ∀ n → Completeᵧ n
complete 0 e = embed (complete₀ e)
complete 1 e = embed (complete₁ e)
complete 2 e = embed (complete₂ e)
complete 3 e = embed (complete₃ e)
complete 4 e = embed (complete₄ e)
complete (suc (suc (suc (suc (suc m))))) e = Theorem.completeᵧ m e
