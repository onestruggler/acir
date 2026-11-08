{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R020 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e29 ; e69)

checked : scaledM (SWAP12) (CZ12 • K12 • CZ12 • K12 • CZ12 • K12) ≡ scaledM (CZ12 • K12 • CZ12 • K12 • CZ12 • K12) (SWAP12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CZ12 • K12 • CZ12 • K12 • CZ12 • K12))) e29)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (SWAP12))) e69)))
