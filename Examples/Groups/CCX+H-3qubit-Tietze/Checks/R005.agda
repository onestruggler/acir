{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R005 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e17 ; e21)

checked : scaledM (CX20) (X1 • CCX12 • X1 • CCX12) ≡ scaledM (X1 • CCX12 • X1 • CCX12) (CX20)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (X1 • CCX12 • X1 • CCX12))) e17)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX20))) e21)))
