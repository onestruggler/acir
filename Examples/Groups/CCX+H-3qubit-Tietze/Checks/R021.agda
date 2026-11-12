{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R021 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e70 ; e71)

checked : scaledM (X0 • X0) (ε) ≡ scaledM (ε) (X0 • X0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (ε))) e70)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (X0 • X0))) e71)))
