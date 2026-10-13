{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R108 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e259 ; e71)

checked : scaledM (H2 • H2) (ε) ≡ scaledM (ε) (H2 • H2)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (ε))) e259)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • H2))) e71)))
