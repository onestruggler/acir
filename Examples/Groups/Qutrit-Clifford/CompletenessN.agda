------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on any number of qutrits
--
-- The box relations on one, two and three qutrits are derived from the
-- rules (Box1, Box2, Box3), so completeness holds outright at every
-- width: two n-qutrit circuits with the same matrix are equal by the
-- 18 rules of Figure 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.CompletenessN where

open import Data.Nat.Base using (ℕ)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics using (⟦_⟧ ; _≈_)
open import Examples.Groups.Qutrit-Clifford.Rels using (rels)
open import Examples.Groups.Qutrit-Clifford.Completeness using (completeness)
open import Examples.Groups.Qutrit-Clifford.Box1 using (br₁)
open import Examples.Groups.Qutrit-Clifford.Box2 using (br₂)
open import Examples.Groups.Qutrit-Clifford.Box3 using (br₃)

complete : (n : ℕ) {w v : Circuit n} → ⟦ w ⟧ ≈ ⟦ v ⟧ → n ⊢ w ≈ v
complete n = completeness (rels br₁ br₂ br₃ n)
