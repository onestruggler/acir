{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R012 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e41 ; e43)

checked : scaledM (CX10) (K01 • CX01 • K01) ≡ scaledM (K01 • CX01 • K01) (CX10)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K01 • CX01 • K01))) e41)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX10))) e43)))
