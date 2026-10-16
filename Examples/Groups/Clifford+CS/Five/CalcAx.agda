------------------------------------------------------------------------
-- Presentations of groups
--
-- The λ-calculus at control wire 4 for generators
--
-- (F4) λ⁰(g) and λ¹(h) commute, (F5) g is λ⁰(g) λ¹(g), for every pair
-- of generators of Circuit 4, and X on wire 4 squares to ε: the joint
-- paper's items when the pair has a CS, a window otherwise (the lemmas
-- `lem-calc-…` of Five.D).  `module At c4` instantiates Five.Calc.
-- Written by `scratchpad/five/calc5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.CalcAx where

open import Data.List using (List ; [] ; _∷_)
open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁ ; λᵈ)
import Examples.Groups.Clifford+CS.Five.Calc
open import Examples.Groups.Clifford+CS.Five.D.D232 using (lem-calc-F4-I-CS01 ; lem-calc-F4-I-CS12 ; lem-calc-F4-I-CS23 ; lem-calc-F4-I-I ; lem-calc-F4-I-K0 ; lem-calc-F4-I-K1 ; lem-calc-F4-I-K2 ; lem-calc-F4-I-K3 ; lem-calc-F4-I-S0 ; lem-calc-F4-I-S1 ; lem-calc-F4-I-S2 ; lem-calc-F4-I-S3)
open import Examples.Groups.Clifford+CS.Five.D.D233 using (lem-calc-F4-K0-CS01 ; lem-calc-F4-K0-CS12 ; lem-calc-F4-K0-CS23 ; lem-calc-F4-K0-I ; lem-calc-F4-K0-K0 ; lem-calc-F4-K0-K1 ; lem-calc-F4-K0-K2 ; lem-calc-F4-K0-K3 ; lem-calc-F4-K0-S0 ; lem-calc-F4-K0-S1 ; lem-calc-F4-K0-S2 ; lem-calc-F4-K0-S3 ; lem-calc-F4-K1-CS01 ; lem-calc-F4-K1-CS12 ; lem-calc-F4-K1-CS23 ; lem-calc-F4-K1-I ; lem-calc-F4-K1-K0 ; lem-calc-F4-K1-K1 ; lem-calc-F4-K1-K2 ; lem-calc-F4-K1-K3 ; lem-calc-F4-K1-S0 ; lem-calc-F4-K1-S1 ; lem-calc-F4-K1-S2 ; lem-calc-F4-K1-S3 ; lem-calc-F4-K2-I ; lem-calc-F4-K2-K0 ; lem-calc-F4-K2-S0 ; lem-calc-F4-K2-S1 ; lem-calc-F4-S0-CS01 ; lem-calc-F4-S0-CS12 ; lem-calc-F4-S0-CS23 ; lem-calc-F4-S0-I ; lem-calc-F4-S0-K0 ; lem-calc-F4-S0-K1 ; lem-calc-F4-S0-K2 ; lem-calc-F4-S0-K3 ; lem-calc-F4-S0-S0 ; lem-calc-F4-S0-S1 ; lem-calc-F4-S0-S2 ; lem-calc-F4-S0-S3 ; lem-calc-F4-S1-CS01 ; lem-calc-F4-S1-CS12 ; lem-calc-F4-S1-CS23 ; lem-calc-F4-S1-I ; lem-calc-F4-S1-K0 ; lem-calc-F4-S1-K1 ; lem-calc-F4-S1-K2 ; lem-calc-F4-S1-K3 ; lem-calc-F4-S1-S0 ; lem-calc-F4-S1-S1 ; lem-calc-F4-S1-S2 ; lem-calc-F4-S1-S3 ; lem-calc-F4-S2-CS01 ; lem-calc-F4-S2-CS12 ; lem-calc-F4-S2-CS23 ; lem-calc-F4-S2-I ; lem-calc-F4-S2-K0 ; lem-calc-F4-S2-K1 ; lem-calc-F4-S2-K2 ; lem-calc-F4-S2-K3 ; lem-calc-F4-S2-S0 ; lem-calc-F4-S2-S1 ; lem-calc-F4-S2-S2 ; lem-calc-F4-S2-S3)
open import Examples.Groups.Clifford+CS.Five.D.D234 using (lem-calc-F4-CS01-CS01 ; lem-calc-F4-CS01-CS12 ; lem-calc-F4-CS01-CS23 ; lem-calc-F4-CS01-I ; lem-calc-F4-CS01-K0 ; lem-calc-F4-CS01-K1 ; lem-calc-F4-CS01-K2 ; lem-calc-F4-CS01-K3 ; lem-calc-F4-CS01-S0 ; lem-calc-F4-CS01-S1 ; lem-calc-F4-CS01-S2 ; lem-calc-F4-CS01-S3 ; lem-calc-F4-CS12-CS01 ; lem-calc-F4-CS12-CS12 ; lem-calc-F4-CS12-CS23 ; lem-calc-F4-CS12-I ; lem-calc-F4-CS12-K0 ; lem-calc-F4-CS12-K1 ; lem-calc-F4-CS12-K2 ; lem-calc-F4-CS12-K3 ; lem-calc-F4-CS12-S0 ; lem-calc-F4-CS12-S1 ; lem-calc-F4-CS12-S2 ; lem-calc-F4-CS12-S3 ; lem-calc-F4-CS23-I ; lem-calc-F4-CS23-K0 ; lem-calc-F4-CS23-K1 ; lem-calc-F4-CS23-K2 ; lem-calc-F4-CS23-S0 ; lem-calc-F4-CS23-S1 ; lem-calc-F4-CS23-S2 ; lem-calc-F4-CS23-S3 ; lem-calc-F4-K2-CS01 ; lem-calc-F4-K2-CS12 ; lem-calc-F4-K2-CS23 ; lem-calc-F4-K2-K1 ; lem-calc-F4-K2-K2 ; lem-calc-F4-K2-K3 ; lem-calc-F4-K2-S2 ; lem-calc-F4-K2-S3 ; lem-calc-F4-K3-CS01 ; lem-calc-F4-K3-CS12 ; lem-calc-F4-K3-CS23 ; lem-calc-F4-K3-I ; lem-calc-F4-K3-K0 ; lem-calc-F4-K3-K1 ; lem-calc-F4-K3-K2 ; lem-calc-F4-K3-K3 ; lem-calc-F4-K3-S0 ; lem-calc-F4-K3-S1 ; lem-calc-F4-K3-S2 ; lem-calc-F4-K3-S3 ; lem-calc-F4-S3-CS01 ; lem-calc-F4-S3-CS12 ; lem-calc-F4-S3-CS23 ; lem-calc-F4-S3-I ; lem-calc-F4-S3-K0 ; lem-calc-F4-S3-K1 ; lem-calc-F4-S3-K2 ; lem-calc-F4-S3-K3 ; lem-calc-F4-S3-S0 ; lem-calc-F4-S3-S1 ; lem-calc-F4-S3-S2 ; lem-calc-F4-S3-S3)
open import Examples.Groups.Clifford+CS.Five.D.D235 using (lem-calc-F4-CS23-CS01 ; lem-calc-F4-CS23-CS12 ; lem-calc-F4-CS23-CS23 ; lem-calc-F4-CS23-K3 ; lem-calc-F5-CS01 ; lem-calc-F5-CS12 ; lem-calc-F5-CS23 ; lem-calc-F5-I-0 ; lem-calc-F5-I-1 ; lem-calc-F5-I-2 ; lem-calc-F5-I-3 ; lem-calc-F5-I-4 ; lem-calc-F5-K0 ; lem-calc-F5-K1 ; lem-calc-F5-K2 ; lem-calc-F5-K3 ; lem-calc-F5-S0 ; lem-calc-F5-S1 ; lem-calc-F5-S2 ; lem-calc-F5-S3 ; lem-calc-x4x4)

F4ᵍ : Complete 4 → ∀ g h → ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ h ∷ [] ⟫ʷ ≈ ⟪ λ₁ h ∷ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ
F4ᵍ c4 (gate₀ I-gate) (gate₀ I-gate) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate) (gate₀ I-gate ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate) (gate₀ I-gate ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ S-gate) = lem-calc-F4-I-S0 c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ K-gate) = lem-calc-F4-I-K0 c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ S-gate ↥) = lem-calc-F4-I-S1 c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ K-gate ↥) = lem-calc-F4-I-K1 c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ S-gate ↥ ↥) = lem-calc-F4-I-S2 c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ K-gate ↥ ↥) = lem-calc-F4-I-K2 c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-I-S3 c4
F4ᵍ c4 (gate₀ I-gate) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-I-K3 c4
F4ᵍ c4 (gate₀ I-gate) (gate₂ CS-gate) = lem-calc-F4-I-CS01 c4
F4ᵍ c4 (gate₀ I-gate) (gate₂ CS-gate ↥) = lem-calc-F4-I-CS12 c4
F4ᵍ c4 (gate₀ I-gate) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-I-CS23 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₀ I-gate) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₀ I-gate ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ S-gate) = lem-calc-F4-I-S0 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ K-gate) = lem-calc-F4-I-K0 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ S-gate ↥) = lem-calc-F4-I-S1 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ K-gate ↥) = lem-calc-F4-I-K1 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-I-S2 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-I-K2 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-I-S3 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-I-K3 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₂ CS-gate) = lem-calc-F4-I-CS01 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₂ CS-gate ↥) = lem-calc-F4-I-CS12 c4
F4ᵍ c4 (gate₀ I-gate ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-I-CS23 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₀ I-gate) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ S-gate) = lem-calc-F4-I-S0 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ K-gate) = lem-calc-F4-I-K0 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-I-S1 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-I-K1 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-I-S2 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-I-K2 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-I-S3 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-I-K3 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-I-CS01 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-I-CS12 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-I-CS23 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₀ I-gate) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ S-gate) = lem-calc-F4-I-S0 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ K-gate) = lem-calc-F4-I-K0 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-I-S1 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-I-K1 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-I-S2 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-I-K2 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-I-S3 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-I-K3 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-I-CS01 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-I-CS12 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-I-CS23 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₀ I-gate) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-I-I c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ S-gate) = lem-calc-F4-I-S0 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ K-gate) = lem-calc-F4-I-K0 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-I-S1 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-I-K1 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-I-S2 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-I-K2 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-I-S3 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-I-K3 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-I-CS01 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-I-CS12 c4
F4ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-I-CS23 c4
F4ᵍ c4 (gate₁ S-gate) (gate₀ I-gate) = lem-calc-F4-S0-I c4
F4ᵍ c4 (gate₁ S-gate) (gate₀ I-gate ↥) = lem-calc-F4-S0-I c4
F4ᵍ c4 (gate₁ S-gate) (gate₀ I-gate ↥ ↥) = lem-calc-F4-S0-I c4
F4ᵍ c4 (gate₁ S-gate) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-S0-I c4
F4ᵍ c4 (gate₁ S-gate) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-S0-I c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ S-gate) = lem-calc-F4-S0-S0 c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ K-gate) = lem-calc-F4-S0-K0 c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ S-gate ↥) = lem-calc-F4-S0-S1 c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ K-gate ↥) = lem-calc-F4-S0-K1 c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ S-gate ↥ ↥) = lem-calc-F4-S0-S2 c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ K-gate ↥ ↥) = lem-calc-F4-S0-K2 c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-S0-S3 c4
F4ᵍ c4 (gate₁ S-gate) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-S0-K3 c4
F4ᵍ c4 (gate₁ S-gate) (gate₂ CS-gate) = lem-calc-F4-S0-CS01 c4
F4ᵍ c4 (gate₁ S-gate) (gate₂ CS-gate ↥) = lem-calc-F4-S0-CS12 c4
F4ᵍ c4 (gate₁ S-gate) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-S0-CS23 c4
F4ᵍ c4 (gate₁ K-gate) (gate₀ I-gate) = lem-calc-F4-K0-I c4
F4ᵍ c4 (gate₁ K-gate) (gate₀ I-gate ↥) = lem-calc-F4-K0-I c4
F4ᵍ c4 (gate₁ K-gate) (gate₀ I-gate ↥ ↥) = lem-calc-F4-K0-I c4
F4ᵍ c4 (gate₁ K-gate) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-K0-I c4
F4ᵍ c4 (gate₁ K-gate) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-K0-I c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ S-gate) = lem-calc-F4-K0-S0 c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ K-gate) = lem-calc-F4-K0-K0 c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ S-gate ↥) = lem-calc-F4-K0-S1 c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ K-gate ↥) = lem-calc-F4-K0-K1 c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ S-gate ↥ ↥) = lem-calc-F4-K0-S2 c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ K-gate ↥ ↥) = lem-calc-F4-K0-K2 c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-K0-S3 c4
F4ᵍ c4 (gate₁ K-gate) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-K0-K3 c4
F4ᵍ c4 (gate₁ K-gate) (gate₂ CS-gate) = lem-calc-F4-K0-CS01 c4
F4ᵍ c4 (gate₁ K-gate) (gate₂ CS-gate ↥) = lem-calc-F4-K0-CS12 c4
F4ᵍ c4 (gate₁ K-gate) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-K0-CS23 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₀ I-gate) = lem-calc-F4-S1-I c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₀ I-gate ↥) = lem-calc-F4-S1-I c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-S1-I c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-S1-I c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-S1-I c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ S-gate) = lem-calc-F4-S1-S0 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ K-gate) = lem-calc-F4-S1-K0 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ S-gate ↥) = lem-calc-F4-S1-S1 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ K-gate ↥) = lem-calc-F4-S1-K1 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-S1-S2 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-S1-K2 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-S1-S3 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-S1-K3 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₂ CS-gate) = lem-calc-F4-S1-CS01 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₂ CS-gate ↥) = lem-calc-F4-S1-CS12 c4
F4ᵍ c4 (gate₁ S-gate ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-S1-CS23 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₀ I-gate) = lem-calc-F4-K1-I c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₀ I-gate ↥) = lem-calc-F4-K1-I c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-K1-I c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-K1-I c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-K1-I c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ S-gate) = lem-calc-F4-K1-S0 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ K-gate) = lem-calc-F4-K1-K0 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ S-gate ↥) = lem-calc-F4-K1-S1 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ K-gate ↥) = lem-calc-F4-K1-K1 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-K1-S2 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-K1-K2 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-K1-S3 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-K1-K3 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₂ CS-gate) = lem-calc-F4-K1-CS01 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₂ CS-gate ↥) = lem-calc-F4-K1-CS12 c4
F4ᵍ c4 (gate₁ K-gate ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-K1-CS23 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₀ I-gate) = lem-calc-F4-S2-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-S2-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-S2-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-S2-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-S2-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ S-gate) = lem-calc-F4-S2-S0 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ K-gate) = lem-calc-F4-S2-K0 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-S2-S1 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-S2-K1 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-S2-S2 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-S2-K2 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-S2-S3 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-S2-K3 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-S2-CS01 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-S2-CS12 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-S2-CS23 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₀ I-gate) = lem-calc-F4-K2-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-K2-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-K2-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-K2-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-K2-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ S-gate) = lem-calc-F4-K2-S0 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ K-gate) = lem-calc-F4-K2-K0 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-K2-S1 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-K2-K1 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-K2-S2 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-K2-K2 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-K2-S3 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-K2-K3 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-K2-CS01 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-K2-CS12 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-K2-CS23 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₀ I-gate) = lem-calc-F4-S3-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-S3-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-S3-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-S3-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-S3-I c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ S-gate) = lem-calc-F4-S3-S0 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ K-gate) = lem-calc-F4-S3-K0 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-S3-S1 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-S3-K1 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-S3-S2 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-S3-K2 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-S3-S3 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-S3-K3 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-S3-CS01 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-S3-CS12 c4
F4ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-S3-CS23 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₀ I-gate) = lem-calc-F4-K3-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-K3-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-K3-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-K3-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-K3-I c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ S-gate) = lem-calc-F4-K3-S0 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ K-gate) = lem-calc-F4-K3-K0 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-K3-S1 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-K3-K1 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-K3-S2 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-K3-K2 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-K3-S3 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-K3-K3 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-K3-CS01 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-K3-CS12 c4
F4ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-K3-CS23 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₀ I-gate) = lem-calc-F4-CS01-I c4
F4ᵍ c4 (gate₂ CS-gate) (gate₀ I-gate ↥) = lem-calc-F4-CS01-I c4
F4ᵍ c4 (gate₂ CS-gate) (gate₀ I-gate ↥ ↥) = lem-calc-F4-CS01-I c4
F4ᵍ c4 (gate₂ CS-gate) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-CS01-I c4
F4ᵍ c4 (gate₂ CS-gate) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-CS01-I c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ S-gate) = lem-calc-F4-CS01-S0 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ K-gate) = lem-calc-F4-CS01-K0 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ S-gate ↥) = lem-calc-F4-CS01-S1 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ K-gate ↥) = lem-calc-F4-CS01-K1 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ S-gate ↥ ↥) = lem-calc-F4-CS01-S2 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ K-gate ↥ ↥) = lem-calc-F4-CS01-K2 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-CS01-S3 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-CS01-K3 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₂ CS-gate) = lem-calc-F4-CS01-CS01 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₂ CS-gate ↥) = lem-calc-F4-CS01-CS12 c4
F4ᵍ c4 (gate₂ CS-gate) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-CS01-CS23 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₀ I-gate) = lem-calc-F4-CS12-I c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₀ I-gate ↥) = lem-calc-F4-CS12-I c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-CS12-I c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-CS12-I c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-CS12-I c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ S-gate) = lem-calc-F4-CS12-S0 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ K-gate) = lem-calc-F4-CS12-K0 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ S-gate ↥) = lem-calc-F4-CS12-S1 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ K-gate ↥) = lem-calc-F4-CS12-K1 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-CS12-S2 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-CS12-K2 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-CS12-S3 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-CS12-K3 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₂ CS-gate) = lem-calc-F4-CS12-CS01 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₂ CS-gate ↥) = lem-calc-F4-CS12-CS12 c4
F4ᵍ c4 (gate₂ CS-gate ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-CS12-CS23 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₀ I-gate) = lem-calc-F4-CS23-I c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₀ I-gate ↥) = lem-calc-F4-CS23-I c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₀ I-gate ↥ ↥) = lem-calc-F4-CS23-I c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F4-CS23-I c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F4-CS23-I c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ S-gate) = lem-calc-F4-CS23-S0 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ K-gate) = lem-calc-F4-CS23-K0 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ S-gate ↥) = lem-calc-F4-CS23-S1 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ K-gate ↥) = lem-calc-F4-CS23-K1 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ S-gate ↥ ↥) = lem-calc-F4-CS23-S2 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ K-gate ↥ ↥) = lem-calc-F4-CS23-K2 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F4-CS23-S3 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F4-CS23-K3 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₂ CS-gate) = lem-calc-F4-CS23-CS01 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₂ CS-gate ↥) = lem-calc-F4-CS23-CS12 c4
F4ᵍ c4 (gate₂ CS-gate ↥ ↥) (gate₂ CS-gate ↥ ↥) = lem-calc-F4-CS23-CS23 c4

F5ᵍ : Complete 4 → ∀ g → ⟪ λᵈ g ∷ [] ⟫ʷ ≈ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ g ∷ [] ⟫ʷ
F5ᵍ c4 (gate₀ I-gate) = lem-calc-F5-I-0 c4
F5ᵍ c4 (gate₀ I-gate ↥) = lem-calc-F5-I-1 c4
F5ᵍ c4 (gate₀ I-gate ↥ ↥) = lem-calc-F5-I-2 c4
F5ᵍ c4 (gate₀ I-gate ↥ ↥ ↥) = lem-calc-F5-I-3 c4
F5ᵍ c4 (gate₀ I-gate ↥ ↥ ↥ ↥) = lem-calc-F5-I-4 c4
F5ᵍ c4 (gate₁ S-gate) = lem-calc-F5-S0 c4
F5ᵍ c4 (gate₁ K-gate) = lem-calc-F5-K0 c4
F5ᵍ c4 (gate₁ S-gate ↥) = lem-calc-F5-S1 c4
F5ᵍ c4 (gate₁ K-gate ↥) = lem-calc-F5-K1 c4
F5ᵍ c4 (gate₁ S-gate ↥ ↥) = lem-calc-F5-S2 c4
F5ᵍ c4 (gate₁ K-gate ↥ ↥) = lem-calc-F5-K2 c4
F5ᵍ c4 (gate₁ S-gate ↥ ↥ ↥) = lem-calc-F5-S3 c4
F5ᵍ c4 (gate₁ K-gate ↥ ↥ ↥) = lem-calc-F5-K3 c4
F5ᵍ c4 (gate₂ CS-gate) = lem-calc-F5-CS01 c4
F5ᵍ c4 (gate₂ CS-gate ↥) = lem-calc-F5-CS12 c4
F5ᵍ c4 (gate₂ CS-gate ↥ ↥) = lem-calc-F5-CS23 c4

x4x4 : Complete 4 → ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε
x4x4 c4 = lem-calc-x4x4 c4

module At (c4 : Complete 4) = Examples.Groups.Clifford+CS.Five.Calc (F4ᵍ c4) (F5ᵍ c4) (x4x4 c4)
