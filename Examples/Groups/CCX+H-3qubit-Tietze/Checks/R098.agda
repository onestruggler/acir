{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R098 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e196 ; e200)

checked : scaledM (t12 • NK) (m0 • NK • m0 • NK • m0) ≡ scaledM (m0 • NK • m0 • NK • m0) (t12 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (m0 • NK • m0 • NK • m0))) e196)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t12 • NK))) e200)))
