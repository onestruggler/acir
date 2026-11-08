{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R086 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e141 ; e142)

checked : scaledM (t23 • m0) (m0 • t23) ≡ scaledM (m0 • t23) (t23 • m0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (m0 • t23))) e141)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t23 • m0))) e142)))
