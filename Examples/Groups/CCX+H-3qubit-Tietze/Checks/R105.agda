{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R105 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e253 ; e254)

checked : scaledM (H2 • CCZ) (CCX01 • H2) ≡ scaledM (CCX01 • H2) (H2 • CCZ)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CCX01 • H2))) e253)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • CCZ))) e254)))
