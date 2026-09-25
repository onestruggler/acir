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
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base322 using (AᴾF ; P322)

d322b : ∀ (α γ v : Bool) → Evaluated (AᴾF α false • P322 v γ) (P322 v γ • AᴾF α false)
d322b true  true  true  = evaluated Eq.refl
d322b true  true  false = evaluated Eq.refl
d322b true  false true  = evaluated Eq.refl
d322b true  false false = evaluated Eq.refl
d322b false true  true  = evaluated Eq.refl
d322b false true  false = evaluated Eq.refl
d322b false false true  = evaluated Eq.refl
d322b false false false = evaluated Eq.refl
