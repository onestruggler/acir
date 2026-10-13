{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R015 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e50 ; e52)

checked : scaledM (X2) (SWAP02 • X0 • SWAP02) ≡ scaledM (SWAP02 • X0 • SWAP02) (X2)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP02 • X0 • SWAP02))) e50)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X2))) e52)))
