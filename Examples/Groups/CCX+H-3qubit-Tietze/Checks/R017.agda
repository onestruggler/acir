{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R017 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e56 ; e58)

checked : scaledM (CCX01) (K12 • CCX02 • K12) ≡ scaledM (K12 • CCX02 • K12) (CCX01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K12 • CCX02 • K12))) e56)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CCX01))) e58)))
