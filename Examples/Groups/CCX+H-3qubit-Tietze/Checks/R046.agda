{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R046 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e120 ; e123)

checked : scaledM (CCX01 • CCX02) (CCX02 • CCX01 • CCX02 • CCX01) ≡ scaledM (CCX02 • CCX01 • CCX02 • CCX01) (CCX01 • CCX02)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CCX02 • CCX01 • CCX02 • CCX01))) e120)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CCX01 • CCX02))) e123)))
