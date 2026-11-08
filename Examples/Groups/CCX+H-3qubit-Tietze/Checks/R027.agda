{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R027 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e78 ; e79)

checked : scaledM (X0 • K12) (K12 • X0) ≡ scaledM (K12 • X0) (X0 • K12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K12 • X0))) e78)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X0 • K12))) e79)))
