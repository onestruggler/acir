------------------------------------------------------------------------
-- Presentations of groups
--
-- Four-wire facts for the canonical form of rule (40), decided
--
-- `e-CH₂`: CH from wire 2 onto wire 0 is P ⊗ P on the wires 0 1 around
-- the box on wire 1 controlled by the wires 0 2 (the H gate with one
-- control, Definition 2.4).  The others are what the transport of C339
-- (Col) to the coordinates of rule (40) — the swap of the wires 2 3,
-- then the transposition τ₀₂ — does to X and to P ⊗ P on the wires 1 3.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base40 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (P₁₃)

e-CH₂ : Evaluated {4} (Ex ↑ • CH • Ex ↑) (PP ↓ • (Ex ↓ • (Λ□ 2 ↓ᵏ 1) • Ex ↓) • PP ↓)
e-CH₂ = evaluated Eq.refl

e-X₃ : Evaluated {4} (Ex ↑ ↑ • X ↑ ↑ ↑ • Ex ↑ ↑) (X ↑ ↑)
e-X₃ = evaluated Eq.refl

e-τX : Evaluated {4} (τ₀₂ • X ↑ ↑ • τ₀₂) X
e-τX = evaluated Eq.refl

e-trX : Evaluated {4} (τ₀₂ • (Ex ↑ ↑ • X ↑ ↑ • Ex ↑ ↑) • τ₀₂) (X ↑ ↑ ↑)
e-trX = evaluated Eq.refl

e-trP : Evaluated {4} (τ₀₂ • (Ex ↑ ↑ • P₁₃ • Ex ↑ ↑) • τ₀₂) (PP ↓)
e-trP = evaluated Eq.refl
