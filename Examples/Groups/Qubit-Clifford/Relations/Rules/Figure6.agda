------------------------------------------------------------------------
-- Presentations of groups
--
-- The equations (3.66) to (3.85) of the supplement: the rewrite rules
-- of Figure 6, for gates in front of a D gate or the E gate
--
-- Generated from the derivations in the supplement to Selinger
-- (arXiv:1310.6813); each equation is a list of Engine steps checked
-- by evaluation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Relations.Rules.Figure6 where

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

Eq3-66 : Eqn (₂₊ n)
Eq3-66 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 1 (L18ᵐ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Eq3-67 : Eqn (₂₊ n)
Eq3-67 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-68 : Eqn (₂₊ n)
Eq3-68 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ h₀ ∷ [])
  (s₀ ∷ s₀ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ s₀ ∷ h₀ ∷ h₀ ∷ [])
  ∷ rw 7 (C₂ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ s₀ ∷ h₁ ∷ [])
  ∷ rw 4 (C₇ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 1 (lift⁼ (sym⁼ C₃ᵉ))
  ∷ perm (h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 2 (lift⁼ (sym⁼ C₂ᵉ))
  ∷ rw 0 (sym⁼ C₁ᵉ)
  ∷ perm (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ h₀ ∷ s₁ ∷ h₁ ∷ 𝕨 ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 10 (lift⁼ (sym⁼ L4ᵉ))
  ∷ perm (h₀ ∷ s₁ ∷ h₁ ∷ s₁ ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ h₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 4 (lift⁼ (sym⁼ L10ᵉ))
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 10 (sym⁼ C₃ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 12 (sym⁼ C₂ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ s₁ ∷ h₁ ∷ h₀ ∷ s₁ ∷ s₀ ∷ s₁ ∷ s₀ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 8 (sym⁼ L17ᵐ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ rw 11 (sym⁼ C₇ᵉ)
  ∷ perm (s₀ ∷ s₀ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-69 : Eqn (₂₊ n)
Eq3-69 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ h₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₀ ∷ [])
  ∷ rw 6 (C₂ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-70 : Eqn (₂₊ n)
Eq3-70 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ [])
  (h₁ ∷ s₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ s₀ ∷ [])
  ∷ rw 7 (C₇ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 1 (L16ᵐ)
  ∷ perm (h₁ ∷ s₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Eq3-71 : Eqn (₂₊ n)
Eq3-71 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₀ ∷ [])
  (s₀ ∷ s₀ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ s₀ ∷ h₁ ∷ [])
  ∷ rw 4 (C₇ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 1 (lift⁼ (sym⁼ C₃ᵉ))
  ∷ perm (h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 2 (lift⁼ (sym⁼ C₂ᵉ))
  ∷ rw 0 (sym⁼ C₁ᵉ)
  ∷ perm (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ h₀ ∷ s₁ ∷ h₁ ∷ 𝕨 ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 10 (lift⁼ (sym⁼ L4ᵉ))
  ∷ perm (h₀ ∷ s₁ ∷ h₁ ∷ s₁ ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ h₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 4 (lift⁼ (sym⁼ L10ᵉ))
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 10 (sym⁼ C₃ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 12 (sym⁼ C₂ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ s₁ ∷ h₁ ∷ h₀ ∷ s₁ ∷ s₀ ∷ s₁ ∷ s₀ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 8 (sym⁼ L17ᵐ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ rw 11 (sym⁼ C₇ᵉ)
  ∷ perm (s₀ ∷ s₀ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-72 : Eqn (₂₊ n)
Eq3-72 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ [])
  (s₁ ∷ h₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ s₀ ∷ h₁ ∷ h₀ ∷ s₀ ∷ [])
  ∷ rw 4 (C₇ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ [])
  ∷ rw 1 (L17ᵐ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ s₀ ∷ [])
  ∷ rw 5 (C₂ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ s₀ ∷ h₁ ∷ [])
  ∷ rw 12 (C₇ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 8 (L14ᵐ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ h₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 9 (C₂ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 7 (C₃ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 4 (lift⁼ C₃ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-73 : Eqn (₂₊ n)
Eq3-73 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ [])
  (h₁ ∷ s₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₀ ∷ h₁ ∷ [])
  ∷ rw 1 (L16ᵐ)
  ∷ perm (h₁ ∷ s₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-74 : Eqn (₂₊ n)
Eq3-74 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₁ ∷ [])
  (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ s₁ ∷ [])
  ∷ rw 7 (C₆ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 1 (L16ᵉ)
  ∷ perm (h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (C₂ᵉ)
  ∷ perm (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Eq3-75 : Eqn (₂₊ n)
Eq3-75 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 1 (L16ᵉ)
  ∷ perm (h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 0 (C₂ᵉ)
  ∷ perm (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-76 : Eqn (₂₊ n)
Eq3-76 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ s₁ ∷ [])
  (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ s₀ ∷ h₀ ∷ [])
  ∷ rw 1 (L16ᵉ)
  ∷ perm (h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₀ ∷ h₀ ∷ [])
  ∷ rw 0 (C₂ᵉ)
  ∷ perm (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-77 : Eqn (₂₊ n)
Eq3-77 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₁ ∷ [])
  (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ h₀ ∷ [])
  ∷ rw 1 (L16ᵉ)
  ∷ perm (h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ rw 0 (C₂ᵉ)
  ∷ perm (s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-78 : Eqn (₂₊ n)
Eq3-78 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ c₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ [])
  ∷ rw 7 (C₅ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-79 : Eqn (₂₊ n)
Eq3-79 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  (s₀ ∷ s₀ ∷ s₀ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 4 (C₁₀ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ s₀ ∷ h₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 11 (lift⁼ L5ᵉ)
  ∷ perm (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 0 (C₁ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ s₁ ∷ h₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 1 (C₆ᵉ)
  ∷ perm (h₀ ∷ s₁ ∷ c₀ ∷ s₁ ∷ h₀ ∷ s₀ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 2 (C₆ᵉ)
  ∷ perm (h₀ ∷ s₁ ∷ s₁ ∷ c₀ ∷ s₁ ∷ h₀ ∷ s₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 3 (C₆ᵉ)
  ∷ perm (h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 7 (sym⁼ C₇ᵉ)
  ∷ perm (h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ s₀ ∷ [])
  ∷ rw 4 (L16ᵉ)
  ∷ perm (s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₀ ∷ [])
  ∷ rw 3 (C₂ᵉ)
  ∷ perm (s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₁ ∷ [])
  ∷ rw 8 (C₇ᵉ)
  ∷ perm (s₀ ∷ h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 2 (lift⁼ (sym⁼ C₂ᵉ))
  ∷ rw 0 (sym⁼ C₁ᵉ)
  ∷ perm (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ s₀ ∷ h₀ ∷ h₁ ∷ 𝕨 ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 10 (lift⁼ (sym⁼ L4ᵉ))
  ∷ perm (s₀ ∷ h₀ ∷ h₁ ∷ s₁ ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ h₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 4 (lift⁼ (sym⁼ L10ᵉ))
  ∷ perm (s₀ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 10 (sym⁼ C₃ᵉ)
  ∷ perm (s₀ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 12 (sym⁼ C₂ᵉ)
  ∷ perm (s₀ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ s₁ ∷ h₁ ∷ h₀ ∷ s₁ ∷ s₀ ∷ s₁ ∷ s₀ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 8 (sym⁼ L17ᵐ)
  ∷ perm (s₀ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ rw 11 (sym⁼ C₇ᵉ)
  ∷ perm (s₀ ∷ s₀ ∷ s₀ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-80 : Eqn (₂₊ n)
Eq3-80 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ s₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  (s₀ ∷ s₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ s₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 4 (C₇ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 1 (L17ᵐ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 5 (C₂ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 12 (C₁₀ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₀ ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ s₀ ∷ h₁ ∷ s₁ ∷ h₁ ∷ s₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 19 (lift⁼ L5ᵉ)
  ∷ perm (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 0 (C₁ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 8 (L14ᵐ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₁ ∷ s₁ ∷ h₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 9 (C₂ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 7 (C₃ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 4 (lift⁼ C₃ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ h₀ ∷ c₀ ∷ s₁ ∷ h₀ ∷ s₁ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 4 (C₆ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ h₀ ∷ s₁ ∷ c₀ ∷ s₁ ∷ h₀ ∷ s₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 5 (C₆ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ s₁ ∷ h₀ ∷ s₁ ∷ s₁ ∷ c₀ ∷ s₁ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 6 (C₆ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ h₀ ∷ s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 3 (lift⁼ C₃ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  ∷ rw 3 (L16ᵉ)
  ∷ perm (s₁ ∷ h₁ ∷ h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 2 (C₂ᵉ)
  ∷ perm (s₀ ∷ s₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Eq3-81 : Eqn (₂₊ n)
Eq3-81 = derive
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Eq3-82 : Eqn (₁₊ n)
Eq3-82 = derive
  (s₀ ∷ [])
  (s₀ ∷ [])
  ( perm (s₀ ∷ [])
  ∷ [])
  Eq.refl

Eq3-83 : Eqn (₁₊ n)
Eq3-83 = derive
  (s₀ ∷ s₀ ∷ [])
  (s₀ ∷ s₀ ∷ [])
  ( perm (s₀ ∷ s₀ ∷ [])
  ∷ [])
  Eq.refl

Eq3-84 : Eqn (₁₊ n)
Eq3-84 = derive
  (s₀ ∷ s₀ ∷ s₀ ∷ [])
  (s₀ ∷ s₀ ∷ s₀ ∷ [])
  ( perm (s₀ ∷ s₀ ∷ s₀ ∷ [])
  ∷ [])
  Eq.refl

Eq3-85 : Eqn (₁₊ n)
Eq3-85 = derive
  (s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
  []
  ( perm (s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
  ∷ rw 0 (C₃ᵉ)
  ∷ perm []
  ∷ [])
  Eq.refl
