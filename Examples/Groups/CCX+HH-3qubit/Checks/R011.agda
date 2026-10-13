{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R011 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e38 ; e40)

checked : scaledM (K01) (SWAP02 • K12 • SWAP02) ≡ scaledM (SWAP02 • K12 • SWAP02) (K01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP02 • K12 • SWAP02))) e38)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (K01))) e40)))
