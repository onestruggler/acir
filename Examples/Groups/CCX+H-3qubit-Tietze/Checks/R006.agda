{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R006 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e22 ; e25)

checked : scaledM (CX21) (CX20 • CX01 • CX20 • CX01) ≡ scaledM (CX20 • CX01 • CX20 • CX01) (CX21)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CX20 • CX01 • CX20 • CX01))) e22)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX21))) e25)))
