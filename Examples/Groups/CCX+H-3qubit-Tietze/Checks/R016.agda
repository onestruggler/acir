{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R016 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e53 ; e55)

checked : scaledM (Z2) (SWAP02 • Z0 • SWAP02) ≡ scaledM (SWAP02 • Z0 • SWAP02) (Z2)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP02 • Z0 • SWAP02))) e53)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (Z2))) e55)))
