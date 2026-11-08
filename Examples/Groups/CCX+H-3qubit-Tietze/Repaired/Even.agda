------------------------------------------------------------------------
-- Presentations of groups
--
-- Even H₂ normal forms, and the type of the step that compares two of
-- them by dyadic completeness.
--
-- The nine Hadamard relations (HadamardRelations/) take that step as a
-- module parameter, so each checks against these light modules (about a
-- thousand interfaces) rather than against dyadic completeness, which
-- imports TwoLevel and so all eight thousand transport certificates.
-- Their one client, Repaired.TwoLevelScaled, applies them to
-- EvenCompleteness.from-even.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.Even where

open import Data.Bool.Base using (false ; true)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Matrix using (⟦_⟧ᴹ)
import Examples.Groups.CCX+HH-3qubit.Normalization as N
open import Presentation.Base _===_ hiding (_===_ ; _≈_)

even : ∀ {w} (nf : N.Normal w) → N.Normal.odd nf ≡ false →
       w ≈ N.dyadic (N.Normal.body nf)
even (N.normal b false e) Eq.refl = trans (lift e) right-unit
even (N.normal b true e) ()

FromEven : Set
FromEven = ∀ {w v} (b c : Word N.DGen) →
           w ≈ N.dyadic b → v ≈ N.dyadic c →
           ⟦ w ⟧ᴹ ≡ ⟦ v ⟧ᴹ → w ≈ v
