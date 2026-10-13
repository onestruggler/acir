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
open import Examples.Groups.Real-Clifford+CH.CommEval
  using (allComm ; reads ; comm-family ; bools ; ∈-bools ; bools₂ ; ∈-bools₂ ; bools₃ ; ∈-bools₃)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; B₁)

-- The family is decided by one boolean, each factor read once
-- (CommEval).
private
  C336 : Bool → Bool → Bool → Circuit 4
  C336 a b c = col (a ∷ true ∷ b ∷ c ∷ []) (B₁ 1)

  all336 : allComm (reads (Λ□ 3 ∷ [])) (reads (bools₃ C336)) ≡ true
  all336 = Eq.refl

d336 : ∀ (a : Bool) (r : Bits 2) → Evaluated (Λ□ 3 • col (a ∷ true ∷ r) (B₁ 1)) (col (a ∷ true ∷ r) (B₁ 1) • Λ□ 3)
d336 a (b ∷ c ∷ []) = comm-family (Λ□ 3 ∷ []) (bools₃ C336) all336 (here Eq.refl) (∈-bools₃ C336 a b c)
