{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R034 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e14 ; e93)

checked : scaledM (Z1) (SWAP01 • Z0 • SWAP01) ≡ scaledM (SWAP01 • Z0 • SWAP01) (Z1)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP01 • Z0 • SWAP01))) e14)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (Z1))) e93)))
