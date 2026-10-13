{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R094 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e171 ; e172)

checked : scaledM (m4 • NK) (NK • m4) ≡ scaledM (NK • m4) (m4 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • m4))) e171)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (m4 • NK))) e172)))
