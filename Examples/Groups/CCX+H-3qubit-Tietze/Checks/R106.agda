{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R106 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e255 ; e256)

checked : scaledM (H2 • K12) (K12 • H2) ≡ scaledM (K12 • H2) (H2 • K12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K12 • H2))) e255)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • K12))) e256)))
