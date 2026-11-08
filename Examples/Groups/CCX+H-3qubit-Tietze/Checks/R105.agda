{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R105 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e253 ; e254)

checked : scaledM (H2 • CCZ) (CCX01 • H2) ≡ scaledM (CCX01 • H2) (H2 • CCZ)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CCX01 • H2))) e253)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • CCZ))) e254)))
