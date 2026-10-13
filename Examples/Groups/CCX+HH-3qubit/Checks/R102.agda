{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R102 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e243 ; e244)

checked : scaledM (H2 • X0) (X0 • H2) ≡ scaledM (X0 • H2) (H2 • X0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (X0 • H2))) e243)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • X0))) e244)))
