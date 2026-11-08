{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R041 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e106 ; e107)

checked : scaledM (K01 • Z0) (X0 • K01) ≡ scaledM (X0 • K01) (K01 • Z0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (X0 • K01))) e106)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (K01 • Z0))) e107)))
