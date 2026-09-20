------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-wire evaluation behind Equation (203)
--
-- Kept apart from the derivation that uses it, as in Evals181: some
-- three hundred stored 8 × 8 matrices, minutes of conversion checking.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Evals203
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃

-- On the wires bottom, middle, top.  The doubly controlled rotation of
-- the top wire from the bottom and middle ones, between P ⊗ P on the
-- outer pair: the CH from the top wire to the bottom one around the HC of
-- the upper pair.
Ŵᶜ₀ : Circuit 3
Ŵᶜ₀ = O₀ CH • U₀ HC • O₀ CH • U₀ HC

-- The doubly controlled rotation of the top wire by H, from the bottom
-- wire and, negatively, the middle one.
°R′₀ : Circuit 3
°R′₀ = O₀ CZ • U₀ HC° • O₀ CZ • U₀ HC°

-- A black control on the middle wire against a white one.
ev-203 : Evaluated (Ŵᶜ₀ • °R′₀) (°R′₀ • Ŵᶜ₀)
ev-203 = evaluated Eq.refl
