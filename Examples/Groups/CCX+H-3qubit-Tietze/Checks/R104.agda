{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H-3qubit-Tietze.Checks.R104 where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Examples.Groups.CCX+H-3qubit-Tietze.Syntactics
open import Examples.Groups.CCX+H-3qubit-Tietze.Interpretation
open import Examples.Groups.CCX+H-3qubit-Tietze.GateMatrices using (√2^_)
open import Examples.Groups.CCX+H-3qubit-Tietze.Semantics using (scaleM)
open import Examples.Groups.CCX+H-3qubit-Tietze.Evaluation using (e247 ; e252)

checked : scaledM (H2 • CCX12) (K01 • K12 • CCZ • K12 • K01 • H2) ≡ scaledM (K01 • K12 • CCZ • K12 • K01 • H2) (H2 • CCX12)
checked = Eq.trans (Eq.cong (scaleM (√2^ len (K01 • K12 • CCZ • K12 • K01 • H2))) e247)
  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len (H2 • CCX12))) e252)))
