{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R108 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e259 ; e71)

checked : scaledM (H2 • H2) (ε) ≡ scaledM (ε) (H2 • H2)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (ε))) e259)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • H2))) e71)))
