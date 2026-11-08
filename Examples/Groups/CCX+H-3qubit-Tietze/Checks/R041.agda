{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R041 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e106 ; e107)

checked : scaledM (K01 • Z0) (X0 • K01) ≡ scaledM (X0 • K01) (K01 • Z0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (X0 • K01))) e106)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (K01 • Z0))) e107)))
