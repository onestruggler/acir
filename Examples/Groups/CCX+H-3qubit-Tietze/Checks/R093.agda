{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R093 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e167 ; e168)

checked : scaledM (t67 • NK) (NK • t67) ≡ scaledM (NK • t67) (t67 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • t67))) e167)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (t67 • NK))) e168)))
