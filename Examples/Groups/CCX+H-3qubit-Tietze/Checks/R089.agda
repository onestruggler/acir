{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R089 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e159 ; e160)

checked : scaledM (t56 • m0) (m0 • t56) ≡ scaledM (m0 • t56) (t56 • m0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (m0 • t56))) e159)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t56 • m0))) e160)))
