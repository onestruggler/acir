{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R098 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e196 ; e200)

checked : scaledM (t12 • NK) (m0 • NK • m0 • NK • m0) ≡ scaledM (m0 • NK • m0 • NK • m0) (t12 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (m0 • NK • m0 • NK • m0))) e196)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t12 • NK))) e200)))
