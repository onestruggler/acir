{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R034 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e14 ; e93)

checked : scaledM (Z1) (SWAP01 • Z0 • SWAP01) ≡ scaledM (SWAP01 • Z0 • SWAP01) (Z1)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP01 • Z0 • SWAP01))) e14)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (Z1))) e93)))
