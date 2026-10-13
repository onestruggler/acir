{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R039 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e102 ; e103)

checked : scaledM (K01 • K12) (K12 • K01) ≡ scaledM (K12 • K01) (K01 • K12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K12 • K01))) e102)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (K01 • K12))) e103)))
