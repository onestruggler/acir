{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R037 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e98 ; e99)

checked : scaledM (X0 • CCX12) (CCX12 • X0) ≡ scaledM (CCX12 • X0) (X0 • CCX12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CCX12 • X0))) e98)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X0 • CCX12))) e99)))
