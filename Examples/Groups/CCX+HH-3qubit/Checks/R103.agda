{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R103 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e245 ; e246)

checked : scaledM (H2 • CX01) (CX01 • H2) ≡ scaledM (CX01 • H2) (H2 • CX01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CX01 • H2))) e245)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • CX01))) e246)))
