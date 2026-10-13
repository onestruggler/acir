------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on two qutrits
--
-- The box relations on one and two qutrits are derived from C₁–C₁₄
-- (Box1, Box2), so completeness holds outright on two qutrits: two
-- circuits with the same matrix are equal by the rules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Completeness2 where

open import Data.Product.Base using (_,_)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics using (⟦_⟧ ; _≈_)
open import Examples.Groups.Qutrit-Clifford.Completeness using (completeness)
open import Examples.Groups.Qutrit-Clifford.Box1 using (br₁)
open import Examples.Groups.Qutrit-Clifford.Box2 using (br₂)

completeness₂ : {w v : Circuit 2} → ⟦ w ⟧ ≈ ⟦ v ⟧ → 2 ⊢ w ≈ v
completeness₂ = completeness (br₁ , br₂)
