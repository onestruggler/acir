------------------------------------------------------------------------
-- Presentations of groups
--
-- The equations (3.1) and (3.2) of the supplement, which bring the
-- identity to normal form (Proposition 6.3)
--
-- Generated from the derivations in the supplement to Selinger
-- (arXiv:1310.6813); each equation is a list of Engine steps checked
-- by evaluation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Relations.Rules.Identity where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
import Relation.Binary.PropositionalEquality as Eq

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Engine
open import Examples.Groups.Qubit-Clifford.Axioms
open import Examples.Groups.Qubit-Clifford.Relations.Lemmas

private
  variable
    n : ℕ

Eq3-1 : Eqn (₁₊ n)
Eq3-1 = derive
  []
  []
  ( perm []
  ∷ [])
  Eq.refl

Eq3-2 : Eqn (₂₊ n)
Eq3-2 = derive
  []
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm []
  ∷ rw 0 (sym⁼ C₂ᵉ)
  ∷ perm (h₀ ∷ h₀ ∷ [])
  ∷ rw 1 (sym⁼ C₅ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 2 (lift⁼ (sym⁼ C₂ᵉ))
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 4 (sym⁼ C₂ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 4 (sym⁼ C₅ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 5 (lift⁼ (sym⁼ C₂ᵉ))
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 7 (sym⁼ C₂ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 7 (sym⁼ C₅ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl
