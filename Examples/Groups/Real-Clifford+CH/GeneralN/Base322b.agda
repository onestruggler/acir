------------------------------------------------------------------------
-- Presentations of groups
--
-- (322) and (323) on four wires, the first gate white on wire 1,
-- decided (Clément, Lemma D.12)
--
-- As Base322, with the rotation's control on wire 1 white.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Base322b where

open import Data.Bool using (Bool ; true ; false)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.CommEval
  using (allComm ; reads ; comm-family ; bools ; ∈-bools ; bools₂ ; ∈-bools₂ ; bools₃ ; ∈-bools₃)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base322 using (AᴾF ; P322)

-- The family is decided by one boolean, each factor read once
-- (CommEval).
private
  all322b : allComm (reads (bools (λ α → AᴾF α false))) (reads (bools₂ P322)) ≡ true
  all322b = Eq.refl

d322b : ∀ (α γ v : Bool) → Evaluated (AᴾF α false • P322 v γ) (P322 v γ • AᴾF α false)
d322b α γ v = comm-family (bools (λ α → AᴾF α false)) (bools₂ P322) all322b
                          (∈-bools (λ α → AᴾF α false) α) (∈-bools₂ P322 v γ)
