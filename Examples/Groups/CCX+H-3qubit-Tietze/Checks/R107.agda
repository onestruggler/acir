{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R107 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e257 ; e258)

checked : scaledM (H2 • NK) (NK • H2) ≡ scaledM (NK • H2) (H2 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • H2))) e257)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • NK))) e258)))
