{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R043 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e110 ; e112)

checked : scaledM (CX01 • CZ12) (CZ12 • CZ02 • CX01) ≡ scaledM (CZ12 • CZ02 • CX01) (CX01 • CZ12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CZ12 • CZ02 • CX01))) e110)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX01 • CZ12))) e112)))
