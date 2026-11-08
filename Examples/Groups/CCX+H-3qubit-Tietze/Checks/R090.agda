{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R090 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e161 ; e162)

checked : scaledM (t67 • m0) (m0 • t67) ≡ scaledM (m0 • t67) (t67 • m0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (m0 • t67))) e161)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t67 • m0))) e162)))
