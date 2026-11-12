{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R001 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e0 ; e4)

checked : scaledM (CZ01) (K12 • CX01 • K12) ≡ scaledM (K12 • CX01 • K12) (CZ01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K12 • CX01 • K12))) e0)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CZ01))) e4)))
