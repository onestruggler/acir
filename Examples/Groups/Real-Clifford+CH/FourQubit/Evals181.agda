------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-wire evaluations behind Equation (181)
--
-- Kept apart from the derivation that uses them: each is a product of a
-- hundred or more stored 8 × 8 matrices, minutes of conversion checking,
-- and a module is re-checked whole.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Evals181
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃

-- P ⊗ P on the outer pair turns the HC of the upper pair (control on
-- the middle wire, H on the top one) into its CZ.
ev-PP-HC : Evaluated (O₀ PP • U₀ HC • O₀ PP) (U₀ CZ)
ev-PP-HC = evaluated Eq.refl

-- The doubly controlled rotation on the top wire, from the bottom wire
-- and, negatively, the middle one.
°R₀ : Circuit 3
°R₀ = U₀ CZ° • O₀ HC • U₀ CZ° • O₀ HC

-- It passes CCZX: (139), (140) in another position.
ev-°R-CCZX : Evaluated (°R₀ • CCZX) (CCZX • °R₀)
ev-°R-CCZX = evaluated Eq.refl

-- The rule (17) on the wires bottom ← top ← middle: the CZ of the lower
-- pair, negated on the middle wire, passes the outer CH around the HC of
-- the upper pair.
ev-17 : Evaluated (L₀ °CZ • (O₀ CH • U₀ HC • O₀ CH)) ((O₀ CH • U₀ HC • O₀ CH) • L₀ °CZ)
ev-17 = evaluated Eq.refl
