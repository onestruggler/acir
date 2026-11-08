{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R015 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e50 ; e52)

checked : scaledM (X2) (SWAP02 • X0 • SWAP02) ≡ scaledM (SWAP02 • X0 • SWAP02) (X2)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP02 • X0 • SWAP02))) e50)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X2))) e52)))
