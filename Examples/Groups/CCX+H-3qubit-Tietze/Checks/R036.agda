{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R036 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e96 ; e97)

checked : scaledM (CCX12 • CX10) (CX10 • CCX12) ≡ scaledM (CX10 • CCX12) (CCX12 • CX10)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CX10 • CCX12))) e96)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CCX12 • CX10))) e97)))
