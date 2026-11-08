{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R011 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e38 ; e40)

checked : scaledM (K01) (SWAP02 • K12 • SWAP02) ≡ scaledM (SWAP02 • K12 • SWAP02) (K01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP02 • K12 • SWAP02))) e38)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (K01))) e40)))
