{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R026 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e76 ; e77)

checked : scaledM (CX12 • X0) (X0 • CX12) ≡ scaledM (X0 • CX12) (CX12 • X0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (X0 • CX12))) e76)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX12 • X0))) e77)))
