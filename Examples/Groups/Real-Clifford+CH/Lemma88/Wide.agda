------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 at width 5 + k, from completeness at every smaller width
-- (Clément, Appendix E.5)
--
-- The rules of Figure 8 whose decodings are proved so far with the
-- general-width machinery of GeneralN: (22), from (335) and (336)
-- (BoxComm), and (39), from (338) with x = y (Box338Eq).  Completeness
-- below the width is the paper's own induction (CompletenessInduction).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Notations using (₁₊ ; ₂₊ ; ₄₊)

module Examples.Groups.Real-Clifford+CH.Lemma88.Wide
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (s≤s)

open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm complete₂ complete₃ using (eq335 ; eq336ᶜ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box338Eq complete₂ complete₃ using (module XY)
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule22 as Rule22
import Examples.Groups.Real-Clifford+CH.Lemma88.Rule39 as Rule39

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  -- (22)
  open Rule22 complete₂ complete₃ (canonN k completes) (eq335 k below) (eq336ᶜ k below) public using (e22)

  -- (39)
  open Rule39 {₂₊ k} (XY.core39 k below) public using (e39)
