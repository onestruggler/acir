------------------------------------------------------------------------
-- Retain Section 5.5's defining equation for the global K gate.
-- The relation sets in Figures 4 and 7 omit this equation; the
-- independent interpretation in MissingK witnesses that omission.
-- Adding it does not change the intended matrix group.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Repaired.Syntactics where

open import Examples.Groups.CCX+HH-3qubit.Syntactics public
  hiding (_===_ ; _≈_)
import Examples.Groups.CCX+HH-3qubit.Syntactics as Paper
import Presentation.Base as PB

infix 4 _===_

data _===_ : WRel Gen where
  paper : ∀ {w v} → w Paper.=== v → w === v
  K-definition : K12 === NK • X0 • NK • X0

open PB _===_ public using (_≈_)

lift : ∀ {w v} → w Paper.≈ v → w ≈ v
lift PB.refl = PB.refl
lift (PB.sym e) = PB.sym (lift e)
lift (PB.trans e f) = PB.trans (lift e) (lift f)
lift (PB.cong e f) = PB.cong (lift e) (lift f)
lift PB.assoc = PB.assoc
lift PB.left-unit = PB.left-unit
lift PB.right-unit = PB.right-unit
lift (PB.axiom e) = PB.axiom (paper e)
