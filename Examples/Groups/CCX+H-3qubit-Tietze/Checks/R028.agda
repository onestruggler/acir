{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R028 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e5 ; e81)

checked : scaledM (X1) (SWAP01 • X0 • SWAP01) ≡ scaledM (SWAP01 • X0 • SWAP01) (X1)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP01 • X0 • SWAP01))) e5)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X1))) e81)))
