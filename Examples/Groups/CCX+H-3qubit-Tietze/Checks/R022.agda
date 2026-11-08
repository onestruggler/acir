{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R022 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e72 ; e71)

checked : scaledM (CX01 • CX01) (ε) ≡ scaledM (ε) (CX01 • CX01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (ε))) e72)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX01 • CX01))) e71)))
