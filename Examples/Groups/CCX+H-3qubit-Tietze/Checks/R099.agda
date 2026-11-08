{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R099 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e201 ; e202)

checked : scaledM (t23 • NK) (NK • t13) ≡ scaledM (NK • t13) (t23 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • t13))) e201)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t23 • NK))) e202)))
