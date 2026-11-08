{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R102 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e243 ; e244)

checked : scaledM (H2 • X0) (X0 • H2) ≡ scaledM (X0 • H2) (H2 • X0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (X0 • H2))) e243)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • X0))) e244)))
