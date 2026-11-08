{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R032 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e56 ; e89)

checked : scaledM (CCX01) (SWAP02 • CCX12 • SWAP02) ≡ scaledM (SWAP02 • CCX12 • SWAP02) (CCX01)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP02 • CCX12 • SWAP02))) e56)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CCX01))) e89)))
