{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R042 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e108 ; e109)

checked : scaledM (X0 • CCX01) (CCX01 • CX12 • X0) ≡ scaledM (CCX01 • CX12 • X0) (X0 • CCX01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CCX01 • CX12 • X0))) e108)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X0 • CCX01))) e109)))
