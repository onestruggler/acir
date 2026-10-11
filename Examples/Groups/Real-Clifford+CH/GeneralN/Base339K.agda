------------------------------------------------------------------------
-- Presentations of groups
--
-- P ⊗ P on the wires 1 3 is P ⊗ P on the wires 0 3 times P ⊗ P on the
-- wires 0 1, in either order (Clément, Equation (130) on the wires 0 1
-- 3), decided on four wires
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base339K where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (P₀₃ ; P₁₃)

dK : Evaluated (P₁₃ {0}) (P₀₃ • PP ↓)
dK = evaluated Eq.refl

dK′ : Evaluated (P₁₃ {0}) (PP ↓ • P₀₃)
dK′ = evaluated Eq.refl
