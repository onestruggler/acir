{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R091 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e163 ; e164)

checked : scaledM (t45 • NK) (NK • t45) ≡ scaledM (NK • t45) (t45 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • t45))) e163)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t45 • NK))) e164)))
