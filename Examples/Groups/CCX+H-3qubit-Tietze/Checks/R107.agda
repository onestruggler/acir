{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R107 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e257 ; e258)

checked : scaledM (H2 • NK) (NK • H2) ≡ scaledM (NK • H2) (H2 • NK)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • H2))) e257)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • NK))) e258)))
