{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R014 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e47 ; e49)

checked : scaledM (CCX02) (SWAP01 • CCX12 • SWAP01) ≡ scaledM (SWAP01 • CCX12 • SWAP01) (CCX02)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (SWAP01 • CCX12 • SWAP01))) e47)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (CCX02))) e49)))
