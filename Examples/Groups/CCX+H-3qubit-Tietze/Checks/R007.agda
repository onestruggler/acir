{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R007 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e26 ; e28)

checked : scaledM (CX12) (K12 • CX21 • K12) ≡ scaledM (K12 • CX21 • K12) (CX12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K12 • CX21 • K12))) e26)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX12))) e28)))
