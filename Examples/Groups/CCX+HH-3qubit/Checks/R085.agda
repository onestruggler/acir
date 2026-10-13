{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R085 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e138 ; e139)

checked : scaledM (t12 • m0) (m0 • t12) ≡ scaledM (m0 • t12) (t12 • m0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (m0 • t12))) e138)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t12 • m0))) e139)))
