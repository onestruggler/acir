{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Checks.R104 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Interpretation
open import Examples.Groups.CCX+HH-3qubit.GateMatrices using (√2^_)
open import Examples.Groups.CCX+HH-3qubit.Semantics using (scaleM)
open import Examples.Groups.CCX+HH-3qubit.Evaluation using (e247 ; e252)

checked : scaledM (H2 • CCX12) (K01 • K12 • CCZ • K12 • K01 • H2) ≡ scaledM (K01 • K12 • CCZ • K12 • K01 • H2) (H2 • CCX12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K01 • K12 • CCZ • K12 • K01 • H2))) e247)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • CCX12))) e252)))
