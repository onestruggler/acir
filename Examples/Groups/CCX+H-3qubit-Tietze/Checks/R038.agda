{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R038 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e100 ; e101)

checked : scaledM (X0 • CX10) (CX10 • X0) ≡ scaledM (CX10 • X0) (X0 • CX10)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CX10 • X0))) e100)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X0 • CX10))) e101)))
