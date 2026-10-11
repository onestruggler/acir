------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-wire evaluations behind Equations (229)–(232)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Evals229
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃

-- −Z on the top wire passes the CZ of the outer pair.
ev-Z°-CZ : Evaluated (U₀ (Z° ↑) • O₀ CZ) (O₀ CZ • U₀ (Z° ↑))
ev-Z°-CZ = evaluated Eq.refl

-- The CZ of the outer pair, negated on the top wire, passes the lower CZ.
ev-°CZ-CZ : Evaluated (O₀ °CZ • L₀ CZ) (L₀ CZ • O₀ °CZ)
ev-°CZ-CZ = evaluated Eq.refl

-- The lower CH passes the CH from the top wire negated there.
ev-CH-°CH : Evaluated (L₀ CH • O₀ °CH) (O₀ °CH • L₀ CH)
ev-CH-°CH = evaluated Eq.refl
