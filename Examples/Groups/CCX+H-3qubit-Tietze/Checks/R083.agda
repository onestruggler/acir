{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R083 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e131 ; e71)

checked : scaledM (m0 • m0) (ε) ≡ scaledM (ε) (m0 • m0)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (ε))) e131)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (m0 • m0))) e71)))
