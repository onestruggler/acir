------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-wire evaluation behind Equation (241)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Evals241
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃

-- The doubly controlled ZX with both controls white.
°°CCZX₀ : Circuit 3
°°CCZX₀ = X ↑ • (X ↑ ↑ • CCZX • X ↑ ↑) • X ↑

-- The lower CH passes it: a black control on the middle wire against a
-- white one.
ev-CH-°°CCZX : Evaluated (L₀ CH • °°CCZX₀) (°°CCZX₀ • L₀ CH)
ev-CH-°°CCZX = evaluated Eq.refl
