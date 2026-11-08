{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R045 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e116 ; e119)

checked : scaledM (CCX12 • CX01) (CX01 • CCX02 • CCX12 • CCX02) ≡ scaledM (CX01 • CCX02 • CCX12 • CCX02) (CCX12 • CX01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CX01 • CCX02 • CCX12 • CCX02))) e116)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CCX12 • CX01))) e119)))
