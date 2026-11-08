{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R044 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e113 ; e115)

checked : scaledM (CX12 • CCX12) (CCX12 • CX10 • CX12) ≡ scaledM (CCX12 • CX10 • CX12) (CX12 • CCX12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (CCX12 • CX10 • CX12))) e113)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CX12 • CCX12))) e115)))
