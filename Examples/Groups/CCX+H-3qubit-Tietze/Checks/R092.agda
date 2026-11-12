{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R092 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e165 ; e166)

checked : scaledM (t56 • NK) (NK • t56) ≡ scaledM (NK • t56) (t56 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • t56))) e165)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t56 • NK))) e166)))
