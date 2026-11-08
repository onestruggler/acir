{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R095 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e173 ; e174)

checked : scaledM (m0 • m4) (m4 • m0) ≡ scaledM (m4 • m0) (m0 • m4)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (m4 • m0))) e173)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (m0 • m4))) e174)))
