{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R084 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e133 ; e71)

checked : scaledM (NK • NK) (ε) ≡ scaledM (ε) (NK • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (ε))) e133)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (NK • NK))) e71)))
