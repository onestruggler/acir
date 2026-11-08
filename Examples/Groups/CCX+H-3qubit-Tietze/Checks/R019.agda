{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R019 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e62 ; e64)

checked : scaledM (CZ12) (SWAP01 • CZ02 • SWAP01) ≡ scaledM (SWAP01 • CZ02 • SWAP01) (CZ12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP01 • CZ02 • SWAP01))) e62)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CZ12))) e64)))
