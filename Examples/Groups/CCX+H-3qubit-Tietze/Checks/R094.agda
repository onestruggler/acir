{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R094 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e171 ; e172)

checked : scaledM (m4 • NK) (NK • m4) ≡ scaledM (NK • m4) (m4 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • m4))) e171)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (m4 • NK))) e172)))
