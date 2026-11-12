{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R100 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e215 ; e228)

checked : scaledM (NK • k1345) (k2345 • k0124) ≡ scaledM (k2345 • k0124) (NK • k1345)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (k2345 • k0124))) e215)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (NK • k1345))) e228)))
