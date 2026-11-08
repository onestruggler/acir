{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R096 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e177 ; e178)

checked : scaledM (NK • k4567) (k4567 • NK) ≡ scaledM (k4567 • NK) (NK • k4567)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (k4567 • NK))) e177)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (NK • k4567))) e178)))
