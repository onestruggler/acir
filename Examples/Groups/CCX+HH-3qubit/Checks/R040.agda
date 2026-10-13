{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R040 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e104 ; e105)

checked : scaledM (CZ01 • CZ12) (CZ12 • CZ01) ≡ scaledM (CZ12 • CZ01) (CZ01 • CZ12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CZ12 • CZ01))) e104)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CZ01 • CZ12))) e105)))
