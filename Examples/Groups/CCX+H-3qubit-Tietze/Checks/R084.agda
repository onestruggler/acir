{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R084 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e133 ; e71)

checked : scaledM (NK • NK) (ε) ≡ scaledM (ε) (NK • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (ε))) e133)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (NK • NK))) e71)))
