{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R004 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e14 ; e16)

checked : scaledM (Z1) (K12 • X1 • K12) ≡ scaledM (K12 • X1 • K12) (Z1)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K12 • X1 • K12))) e14)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (Z1))) e16)))
