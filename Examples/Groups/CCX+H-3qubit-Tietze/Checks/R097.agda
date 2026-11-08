{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R097 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e182 ; e195)

checked : scaledM (t01 • NK) (NK • t13 • m1 • m3) ≡ scaledM (NK • t13 • m1 • m3) (t01 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • t13 • m1 • m3))) e182)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t01 • NK))) e195)))
