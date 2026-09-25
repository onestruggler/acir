------------------------------------------------------------------------
-- Presentations of groups
--
-- (336) on four wires, decided (Clément, Lemma D.13)
--
-- The box Λ□ 3 commutes with each colouring of the box on wire 1
-- controlled by wire 0 and the wires 2 3 whose bit on wire 1 is true,
-- by evaluation: with completeness on four wires, an equation.  The
-- other colourings follow by X on wire 1 (GeneralN/BoxComm).  In a
-- module of its own, like Base335.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base336 where

open import Data.Bool using (Bool ; true ; false)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; B₁)

d336 : ∀ (a : Bool) (r : Bits 2) → Evaluated (Λ□ 3 • col (a ∷ true ∷ r) (B₁ 1)) (col (a ∷ true ∷ r) (B₁ 1) • Λ□ 3)
d336 true  (true  ∷ true  ∷ []) = evaluated Eq.refl
d336 true  (true  ∷ false ∷ []) = evaluated Eq.refl
d336 true  (false ∷ true  ∷ []) = evaluated Eq.refl
d336 true  (false ∷ false ∷ []) = evaluated Eq.refl
d336 false (true  ∷ true  ∷ []) = evaluated Eq.refl
d336 false (true  ∷ false ∷ []) = evaluated Eq.refl
d336 false (false ∷ true  ∷ []) = evaluated Eq.refl
d336 false (false ∷ false ∷ []) = evaluated Eq.refl
