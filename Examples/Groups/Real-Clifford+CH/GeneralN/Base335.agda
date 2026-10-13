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
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)

-- The family is decided by one boolean, each factor read once
-- (CommEval).
private
  C335 : Bool → Bool → Bool → Circuit 4
  C335 a b c = col (true ∷ a ∷ b ∷ c ∷ []) (Λ□ 3)

  all335 : allComm (reads (Λ□ 3 ∷ [])) (reads (bools₃ C335)) ≡ true
  all335 = Eq.refl

d335 : ∀ (r : Bits 3) → Evaluated (Λ□ 3 • col (true ∷ r) (Λ□ 3)) (col (true ∷ r) (Λ□ 3) • Λ□ 3)
d335 (a ∷ b ∷ c ∷ []) = comm-family (Λ□ 3 ∷ []) (bools₃ C335) all335 (here Eq.refl) (∈-bools₃ C335 a b c)
