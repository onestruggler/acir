------------------------------------------------------------------------
-- Presentations of groups
--
-- λ¹ on generators, by evaluation (CS)
--
-- The letter λ¹(g) of a four-wire generator g denotes ctrl₁ ⟦ g ⟧: g where
-- wire 4 reads 1, the identity where it reads 0.  Written like
-- Five.Sem.LamEval1 (scratchpad/mklam.py).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.Lam1Eval2 where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics using (Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; I-gate ; S-gate ; K-gate ; CS-gate)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ ; ⟦_⟧ᵍ)
open import Examples.Groups.Clifford+CS.Five.Letters using (⟪_⟫)
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁)
open import Examples.Groups.Clifford+CS.Five.Sem.Ctrl1 using (ctrl₁Op)
open import Examples.Groups.Clifford+CS.Five.Sem.Eval using (SameOp ; same-op)

private
  ev : (g : Gen 4) → SameOp ⟪ λ₁ g ⟫ 1 (ctrl₁Op 1 ⟦ g ⟧ᵍ) → ⟦ ⟪ λ₁ g ⟫ ⟧ ~ (1 , ctrl₁Op 1 ⟦ g ⟧ᵍ)
  ev g e = same-op ⟪ λ₁ g ⟫ 1 (ctrl₁Op 1 ⟦ g ⟧ᵍ) e

lam1-CS : ⟦ ⟪ λ₁ (gate₂ CS-gate) ⟫ ⟧ ~ (1 , ctrl₁Op {4} 1 ⟦ gate₂ CS-gate ⟧ᵍ)
lam1-CS = ev (gate₂ CS-gate) Eq.refl

lam1-CS↑ : ⟦ ⟪ λ₁ (gate₂ CS-gate ↥) ⟫ ⟧ ~ (1 , ctrl₁Op {4} 1 ⟦ gate₂ CS-gate ↥ ⟧ᵍ)
lam1-CS↑ = ev (gate₂ CS-gate ↥) Eq.refl

lam1-CS↑↑ : ⟦ ⟪ λ₁ (gate₂ CS-gate ↥ ↥) ⟫ ⟧ ~ (1 , ctrl₁Op {4} 1 ⟦ gate₂ CS-gate ↥ ↥ ⟧ᵍ)
lam1-CS↑↑ = ev (gate₂ CS-gate ↥ ↥) Eq.refl

