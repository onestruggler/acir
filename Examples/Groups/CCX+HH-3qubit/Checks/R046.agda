{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R046 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e120 ; e123)

checked : scaledM (CCX01 • CCX02) (CCX02 • CCX01 • CCX02 • CCX01) ≡ scaledM (CCX02 • CCX01 • CCX02 • CCX01) (CCX01 • CCX02)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CCX02 • CCX01 • CCX02 • CCX01))) e120)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CCX01 • CCX02))) e123)))
