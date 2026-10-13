{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R003 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e10 ; e13)

checked : scaledM (Z0) (CZ01 • CX01 • CZ01 • CX01) ≡ scaledM (CZ01 • CX01 • CZ01 • CX01) (Z0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CZ01 • CX01 • CZ01 • CX01))) e10)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (Z0))) e13)))
