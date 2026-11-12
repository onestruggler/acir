{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R018 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e59 ; e61)

checked : scaledM (CZ02) (SWAP12 • CZ01 • SWAP12) ≡ scaledM (SWAP12 • CZ01 • SWAP12) (CZ02)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP12 • CZ01 • SWAP12))) e59)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CZ02))) e61)))
