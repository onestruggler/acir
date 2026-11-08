{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R013 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e44 ; e46)

checked : scaledM (SWAP01) (CX01 • CX10 • CX01) ≡ scaledM (CX01 • CX10 • CX01) (SWAP01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CX01 • CX10 • CX01))) e44)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (SWAP01))) e46)))
