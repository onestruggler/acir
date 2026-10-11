------------------------------------------------------------------------
-- Presentations of groups
--
-- Three-wire facts for the canonical form of rule (45), decided
--
-- P ⊗ P on the wires 0 1, on the wires 0 2 (the swap of the wires 1 2
-- around it) and on the wires 1 2 form a Klein four-group ((130)); the
-- swap of the wires 0 1, and the transposition τ₀₂, carry P ⊗ P on the
-- wires 0 2 resp. 0 1 to P ⊗ P on the wires 1 2; and τ₀₂ fixes X on
-- wire 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base45 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)

e-PP₁ : Evaluated {3} (PP ↓ • (Ex ↑ • PP ↓ • Ex ↑)) (PP ↑)
e-PP₁ = evaluated Eq.refl

e-PP₂ : Evaluated {3} ((Ex ↑ • PP ↓ • Ex ↑) • PP ↓) (PP ↑)
e-PP₂ = evaluated Eq.refl

e-PP₃ : Evaluated {3} (Ex ↓ • (Ex ↑ • PP ↓ • Ex ↑) • Ex ↓) (PP ↑)
e-PP₃ = evaluated Eq.refl

e-τP : Evaluated {3} (τ₀₂ • PP ↓ • τ₀₂) (PP ↑)
e-τP = evaluated Eq.refl

e-τX₁ : Evaluated {3} (τ₀₂ • X ↑ • τ₀₂) (X ↑)
e-τX₁ = evaluated Eq.refl
