{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R100 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e215 ; e228)

checked : scaledM (NK • k1345) (k2345 • k0124) ≡ scaledM (k2345 • k0124) (NK • k1345)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (k2345 • k0124))) e215)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (NK • k1345))) e228)))
