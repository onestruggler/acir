{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R009 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e32 ; e34)

checked : scaledM (CX02) (SWAP12 • CX01 • SWAP12) ≡ scaledM (SWAP12 • CX01 • SWAP12) (CX02)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP12 • CX01 • SWAP12))) e32)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX02))) e34)))
