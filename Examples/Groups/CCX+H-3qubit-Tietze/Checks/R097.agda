{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R097 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e182 ; e195)

checked : scaledM (t01 • NK) (NK • t13 • m1 • m3) ≡ scaledM (NK • t13 • m1 • m3) (t01 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • t13 • m1 • m3))) e182)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t01 • NK))) e195)))
