------------------------------------------------------------------------
-- Presentations of groups
--
-- (335) on four wires, decided (Clément, Lemma D.13)
--
-- The box Λ□ 3 commutes with each colouring of itself whose bit on the
-- box wire is true, by evaluation (about four seconds each): with
-- completeness on four wires, an equation.  The other colourings follow
-- by X on the box wire (GeneralN/BoxComm).  In a module of its own:
-- Agda frees the memory of an evaluation only when its module is done.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base335 where

open import Data.Bool using (true ; false)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)

d335 : ∀ (r : Bits 3) → Evaluated (Λ□ 3 • col (true ∷ r) (Λ□ 3)) (col (true ∷ r) (Λ□ 3) • Λ□ 3)
d335 (true  ∷ true  ∷ true  ∷ []) = evaluated Eq.refl
d335 (true  ∷ true  ∷ false ∷ []) = evaluated Eq.refl
d335 (true  ∷ false ∷ true  ∷ []) = evaluated Eq.refl
d335 (true  ∷ false ∷ false ∷ []) = evaluated Eq.refl
d335 (false ∷ true  ∷ true  ∷ []) = evaluated Eq.refl
d335 (false ∷ true  ∷ false ∷ []) = evaluated Eq.refl
d335 (false ∷ false ∷ true  ∷ []) = evaluated Eq.refl
d335 (false ∷ false ∷ false ∷ []) = evaluated Eq.refl
