{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R010 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e35 ; e37)

checked : scaledM (SWAP02) (CX02 • CX20 • CX02) ≡ scaledM (CX02 • CX20 • CX02) (SWAP02)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CX02 • CX20 • CX02))) e35)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (SWAP02))) e37)))
