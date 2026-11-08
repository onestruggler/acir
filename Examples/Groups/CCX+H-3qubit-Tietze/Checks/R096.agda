{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R096 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e177 ; e178)

checked : scaledM (NK • k4567) (k4567 • NK) ≡ scaledM (k4567 • NK) (NK • k4567)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (k4567 • NK))) e177)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (NK • k4567))) e178)))
