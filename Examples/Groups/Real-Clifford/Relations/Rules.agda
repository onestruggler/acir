------------------------------------------------------------------------
-- Presentations of groups
--
-- The typed relations, as used by the normalisation
--
-- Generated from the derivations of the supplement to Makary, Ross and
-- Selinger (arXiv:2109.05655); each equation is a list of Engine steps
-- checked by evaluation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Relations.Rules where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
import Relation.Binary.PropositionalEquality as Eq

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine
open import Examples.Groups.Real-Clifford.Axioms
open import Examples.Groups.Real-Clifford.Relations.Typed
open import Examples.Groups.Real-Clifford.Relations.Derived

private
  variable
    n : ℕ

Rule-ZA-1 : Eqn (₁₊ n)
Rule-ZA-1 = derive
  (z₀ ∷ [])
  (z₀ ∷ [])
  ( perm (z₀ ∷ [])
  ∷ rw 0 (T3-1ᵉ)
  ∷ perm (z₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-ZA-2 : Eqn (₁₊ n)
Rule-ZA-2 = derive
  (h₀ ∷ z₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ [])
  ( perm (h₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T3-3ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-ZA-3 : Eqn (₁₊ n)
Rule-ZA-3 = derive
  (z₀ ∷ [])
  (z₀ ∷ [])
  ( perm (z₀ ∷ [])
  ∷ rw 0 (T3-1ᵉ)
  ∷ perm (z₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-HA-1 : Eqn (₁₊ n)
Rule-HA-1 = derive
  (h₀ ∷ [])
  (h₀ ∷ [])
  ( perm (h₀ ∷ [])
  ∷ rw 0 (T3-2ᵉ)
  ∷ perm (h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-HA-2 : Eqn (₁₊ n)
Rule-HA-2 = derive
  (h₀ ∷ h₀ ∷ [])
  ([])
  ( perm (h₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T3-4ᵉ)
  ∷ perm ([])
  ∷ [])
  Eq.refl

Rule-HA-3 : Eqn (₁₊ n)
Rule-HA-3 = derive
  (h₀ ∷ [])
  (h₀ ∷ [])
  ( perm (h₀ ∷ [])
  ∷ rw 0 (T3-2ᵉ)
  ∷ perm (h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZA^-1 : Eqn (₂₊ n)
Rule-CZA^-1 = derive
  (c₀ ∷ [])
  (c₀ ∷ [])
  ( perm (c₀ ∷ [])
  ∷ rw 0 (T3-7ᵉ)
  ∷ perm (c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZA^-2 : Eqn (₂₊ n)
Rule-CZA^-2 = derive
  (h₁ ∷ c₀ ∷ [])
  (h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-8ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZA^-3 : Eqn (₂₊ n)
Rule-CZA^-3 = derive
  (c₀ ∷ [])
  (z₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ [])
  ∷ rw 0 (T3-9ᵉ)
  ∷ perm (z₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-1-1 : Eqn (₂₊ n)
Rule-CZAB-1-1 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-10ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-2-1 : Eqn (₂₊ n)
Rule-CZAB-2-1 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ [])
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-11ᵉ)
  ∷ perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-1-2 : Eqn (₂₊ n)
Rule-CZAB-1-2 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ [])
  (c₀ ∷ h₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-12ᵉ)
  ∷ perm (c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-2-2 : Eqn (₂₊ n)
Rule-CZAB-2-2 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-13ᵉ)
  ∷ perm (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-1-3 : Eqn (₂₊ n)
Rule-CZAB-1-3 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-14ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-2-3 : Eqn (₂₊ n)
Rule-CZAB-2-3 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-15ᵉ)
  ∷ perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-1-4 : Eqn (₂₊ n)
Rule-CZAB-1-4 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  (h₁ ∷ z₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-16ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-2-4 : Eqn (₂₊ n)
Rule-CZAB-2-4 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-17ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-3-5 : Eqn (₂₊ n)
Rule-CZAB-3-5 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-18ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-3-6 : Eqn (₂₊ n)
Rule-CZAB-3-6 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-19ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-3-7 : Eqn (₂₊ n)
Rule-CZAB-3-7 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (N-CZAB-3-7)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZAB-3-8 : Eqn (₂₊ n)
Rule-CZAB-3-8 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T3-21ᵉ)
  ∷ perm (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0B-5 : Eqn (₂₊ n)
Rule-H0B-5 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T3-22ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0B-6 : Eqn (₂₊ n)
Rule-H0B-6 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 0 (N-H0B-6)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0B-7 : Eqn (₂₊ n)
Rule-H0B-7 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ rw 0 (N-H0B-7)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0B-8 : Eqn (₂₊ n)
Rule-H0B-8 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  (c₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ [])
  ∷ rw 0 (N-H0B-8)
  ∷ perm (c₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-1 : Eqn (₂₊ n)
Rule-X0B-1 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-1ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-2 : Eqn (₂₊ n)
Rule-X0B-2 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-2ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-3 : Eqn (₂₊ n)
Rule-X0B-3 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-3ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-4 : Eqn (₂₊ n)
Rule-X0B-4 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-4ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-5 : Eqn (₂₊ n)
Rule-X0B-5 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-1ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-6 : Eqn (₂₊ n)
Rule-X0B-6 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-2ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-7 : Eqn (₂₊ n)
Rule-X0B-7 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-3ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-X0B-8 : Eqn (₂₊ n)
Rule-X0B-8 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-4ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-1 : Eqn (₂₊ n)
Rule-H1B-1 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-9ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-2 : Eqn (₂₊ n)
Rule-H1B-2 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-12ᵉ)
  ∷ perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-3 : Eqn (₂₊ n)
Rule-H1B-3 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ [])
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-15ᵉ)
  ∷ perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-4 : Eqn (₂₊ n)
Rule-H1B-4 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-18ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-5 : Eqn (₂₊ n)
Rule-H1B-5 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-9ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-6 : Eqn (₂₊ n)
Rule-H1B-6 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-12ᵉ)
  ∷ perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-7 : Eqn (₂₊ n)
Rule-H1B-7 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ [])
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-15ᵉ)
  ∷ perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H1B-8 : Eqn (₂₊ n)
Rule-H1B-8 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  ∷ rw 0 (T4-18ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-1 : Eqn (₂₊ n)
Rule-Z1B-1 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-10ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-2 : Eqn (₂₊ n)
Rule-Z1B-2 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₁ ∷ [])
  (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-13ᵉ)
  ∷ perm (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-3 : Eqn (₂₊ n)
Rule-Z1B-3 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-16ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-4 : Eqn (₂₊ n)
Rule-Z1B-4 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-19ᵉ)
  ∷ perm (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-5 : Eqn (₂₊ n)
Rule-Z1B-5 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-10ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-6 : Eqn (₂₊ n)
Rule-Z1B-6 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₁ ∷ [])
  (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-13ᵉ)
  ∷ perm (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-7 : Eqn (₂₊ n)
Rule-Z1B-7 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-16ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1B-8 : Eqn (₂₊ n)
Rule-Z1B-8 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T4-19ᵉ)
  ∷ perm (z₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-1 : Eqn (₂₊ n)
Rule-Z0B-1 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  (z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-11ᵉ)
  ∷ perm (z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-2 : Eqn (₂₊ n)
Rule-Z0B-2 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-14ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-3 : Eqn (₂₊ n)
Rule-Z0B-3 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-17ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-4 : Eqn (₂₊ n)
Rule-Z0B-4 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ h₁ ∷ z₁ ∷ h₁ ∷ z₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-20ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ h₁ ∷ z₁ ∷ h₁ ∷ z₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-5 : Eqn (₂₊ n)
Rule-Z0B-5 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  (z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-11ᵉ)
  ∷ perm (z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-6 : Eqn (₂₊ n)
Rule-Z0B-6 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-14ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-7 : Eqn (₂₊ n)
Rule-Z0B-7 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-17ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0B-8 : Eqn (₂₊ n)
Rule-Z0B-8 = derive
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ h₁ ∷ z₁ ∷ h₁ ∷ z₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-20ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ z₁ ∷ h₁ ∷ z₁ ∷ h₁ ∷ z₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-ZC-1 : Eqn (₁₊ n)
Rule-ZC-1 = derive
  (z₀ ∷ [])
  (z₀ ∷ [])
  ( perm (z₀ ∷ [])
  ∷ rw 0 (T3-1ᵉ)
  ∷ perm (z₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-XC-1 : Eqn (₁₊ n)
Rule-XC-1 = derive
  (h₀ ∷ z₀ ∷ h₀ ∷ [])
  (h₀ ∷ z₀ ∷ h₀ ∷ [])
  ( perm (h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-34ᵉ)
  ∷ perm (h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-SCZC-1 : Eqn (₂₊ n)
Rule-SCZC-1 = derive
  (c₀ ∷ [])
  (c₀ ∷ [])
  ( perm (c₀ ∷ [])
  ∷ rw 0 (T3-7ᵉ)
  ∷ perm (c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-ZC-2 : Eqn (₁₊ n)
Rule-ZC-2 = derive
  (h₀ ∷ z₀ ∷ h₀ ∷ z₀ ∷ [])
  (𝕞 ∷ z₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ( perm (h₀ ∷ z₀ ∷ h₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T4-36ᵉ)
  ∷ perm (𝕞 ∷ z₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-XC-2 : Eqn (₁₊ n)
Rule-XC-2 = derive
  (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ([])
  ( perm (h₀ ∷ z₀ ∷ h₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T4-37ᵉ)
  ∷ perm ([])
  ∷ [])
  Eq.refl

Rule-SCZC-2 : Eqn (₂₊ n)
Rule-SCZC-2 = derive
  (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ [])
  (z₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ [])
  ( perm (h₁ ∷ z₁ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T4-38ᵉ)
  ∷ perm (z₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-SCZB-1 : Eqn (₃₊ n)
Rule-SCZB-1 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T5-1ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-SCZB-2 : Eqn (₃₊ n)
Rule-SCZB-2 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  (c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T5-2ᵉ)
  ∷ perm (c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-SCZB-3 : Eqn (₃₊ n)
Rule-SCZB-3 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T5-3ᵉ)
  ∷ perm (c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-SCZB-4 : Eqn (₃₊ n)
Rule-SCZB-4 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ [])
  (z₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T5-4ᵉ)
  ∷ perm (z₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-SXZCB-5 : Eqn (₃₊ n)
Rule-SXZCB-5 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  (z₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 0 (N-SXZCB-5)
  ∷ perm (z₀ ∷ z₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-SXZCB-6 : Eqn (₃₊ n)
Rule-SXZCB-6 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 0 (N-SXZCB-6)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-SXZCB-7 : Eqn (₃₊ n)
Rule-SXZCB-7 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 0 (N-SXZCB-7)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-SXZCB-8 : Eqn (₃₊ n)
Rule-SXZCB-8 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  (z₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ [])
  ∷ rw 0 (N-SXZCB-8)
  ∷ perm (z₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-1-1 : Eqn (₃₊ n)
Rule-CZBB-1-1 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-1ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-1-2 : Eqn (₃₊ n)
Rule-CZBB-1-2 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-2ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-1-3 : Eqn (₃₊ n)
Rule-CZBB-1-3 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-3ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-1-4 : Eqn (₃₊ n)
Rule-CZBB-1-4 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-4ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-2-1 : Eqn (₃₊ n)
Rule-CZBB-2-1 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-5ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-2-2 : Eqn (₃₊ n)
Rule-CZBB-2-2 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-6ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-2-3 : Eqn (₃₊ n)
Rule-CZBB-2-3 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-7ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-2-4 : Eqn (₃₊ n)
Rule-CZBB-2-4 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-8ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-3-1 : Eqn (₃₊ n)
Rule-CZBB-3-1 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-9ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-3-2 : Eqn (₃₊ n)
Rule-CZBB-3-2 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-10ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-3-3 : Eqn (₃₊ n)
Rule-CZBB-3-3 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-11ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-3-4 : Eqn (₃₊ n)
Rule-CZBB-3-4 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-12ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-4-5 : Eqn (₃₊ n)
Rule-CZBB-4-5 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-13ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-4-6 : Eqn (₃₊ n)
Rule-CZBB-4-6 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-14ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-4-7 : Eqn (₃₊ n)
Rule-CZBB-4-7 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-15ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-4-8 : Eqn (₃₊ n)
Rule-CZBB-4-8 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-16ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-5-5 : Eqn (₃₊ n)
Rule-CZBB-5-5 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-1ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-5-6 : Eqn (₃₊ n)
Rule-CZBB-5-6 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-2ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-5-7 : Eqn (₃₊ n)
Rule-CZBB-5-7 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-3ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-5-8 : Eqn (₃₊ n)
Rule-CZBB-5-8 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-4ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-6-5 : Eqn (₃₊ n)
Rule-CZBB-6-5 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-5ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-6-6 : Eqn (₃₊ n)
Rule-CZBB-6-6 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-6ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-6-7 : Eqn (₃₊ n)
Rule-CZBB-6-7 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-7ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-6-8 : Eqn (₃₊ n)
Rule-CZBB-6-8 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-8ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-7-5 : Eqn (₃₊ n)
Rule-CZBB-7-5 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-9ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-7-6 : Eqn (₃₊ n)
Rule-CZBB-7-6 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-10ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-7-7 : Eqn (₃₊ n)
Rule-CZBB-7-7 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-11ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-7-8 : Eqn (₃₊ n)
Rule-CZBB-7-8 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-12ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-8-1 : Eqn (₃₊ n)
Rule-CZBB-8-1 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-13ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-8-2 : Eqn (₃₊ n)
Rule-CZBB-8-2 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-14ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-8-3 : Eqn (₃₊ n)
Rule-CZBB-8-3 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-15ᵉ)
  ∷ perm (h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZBB-8-4 : Eqn (₃₊ n)
Rule-CZBB-8-4 = derive
  (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ c₁ ∷ [])
  ∷ rw 0 (T6-16ᵉ)
  ∷ perm (c₀ ∷ h₂ ∷ z₂ ∷ h₂ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1D-1 : Eqn (₂₊ n)
Rule-Z1D-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₁ ∷ [])
  (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T8-1ᵉ)
  ∷ perm (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1D-2 : Eqn (₂₊ n)
Rule-Z1D-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  ∷ rw 0 (T8-3ᵉ)
  ∷ perm (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1D-3 : Eqn (₂₊ n)
Rule-Z1D-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₁ ∷ [])
  (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₁ ∷ [])
  ∷ rw 0 (T8-5ᵉ)
  ∷ perm (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z1D-4 : Eqn (₂₊ n)
Rule-Z1D-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  (z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₁ ∷ [])
  ∷ rw 0 (T8-7ᵉ)
  ∷ perm (z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0D-1 : Eqn (₂₊ n)
Rule-Z0D-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T8-2ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0D-2 : Eqn (₂₊ n)
Rule-Z0D-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  (z₀ ∷ z₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  ∷ rw 0 (T8-4ᵉ)
  ∷ perm (z₀ ∷ z₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0D-3 : Eqn (₂₊ n)
Rule-Z0D-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₀ ∷ [])
  (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T8-6ᵉ)
  ∷ perm (h₁ ∷ z₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-Z0D-4 : Eqn (₂₊ n)
Rule-Z0D-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  (z₁ ∷ z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ z₀ ∷ [])
  ∷ rw 0 (T8-8ᵉ)
  ∷ perm (z₁ ∷ z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0D-1 : Eqn (₂₊ n)
Rule-H0D-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T8-9ᵉ)
  ∷ perm (h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0D-2 : Eqn (₂₊ n)
Rule-H0D-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ rw 0 (T8-11ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0D-3 : Eqn (₂₊ n)
Rule-H0D-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₀ ∷ [])
  ∷ rw 0 (T8-13ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-H0D-4 : Eqn (₂₊ n)
Rule-H0D-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  (h₁ ∷ z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ rw 0 (T8-15ᵉ)
  ∷ perm (h₁ ∷ z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZD-1 : Eqn (₂₊ n)
Rule-CZD-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T8-10ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZD-2 : Eqn (₂₊ n)
Rule-CZD-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  (z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T8-12ᵉ)
  ∷ perm (z₀ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZD-3 : Eqn (₂₊ n)
Rule-CZD-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ rw 0 (T8-14ᵉ)
  ∷ perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZD-4 : Eqn (₂₊ n)
Rule-CZD-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T8-16ᵉ)
  ∷ perm (z₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-ZE-1 : Eqn (₁₊ n)
Rule-ZE-1 = derive
  (z₀ ∷ [])
  (z₀ ∷ [])
  ( perm (z₀ ∷ [])
  ∷ rw 0 (T3-1ᵉ)
  ∷ perm (z₀ ∷ [])
  ∷ [])
  Eq.refl

Rule-ZE-2 : Eqn (₁₊ n)
Rule-ZE-2 = derive
  (z₀ ∷ z₀ ∷ [])
  ([])
  ( perm (z₀ ∷ z₀ ∷ [])
  ∷ rw 0 (T8-18ᵉ)
  ∷ perm ([])
  ∷ [])
  Eq.refl

Rule-CZDD-1-1 : Eqn (₃₊ n)
Rule-CZDD-1-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-1ᵉ)
  ∷ perm (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-1-2 : Eqn (₃₊ n)
Rule-CZDD-1-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  (h₂ ∷ c₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-2ᵉ)
  ∷ perm (h₂ ∷ c₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-1-3 : Eqn (₃₊ n)
Rule-CZDD-1-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-3ᵉ)
  ∷ perm (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-1-4 : Eqn (₃₊ n)
Rule-CZDD-1-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  (h₂ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-4ᵉ)
  ∷ perm (h₂ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-2-1 : Eqn (₃₊ n)
Rule-CZDD-2-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-5ᵉ)
  ∷ perm (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-2-2 : Eqn (₃₊ n)
Rule-CZDD-2-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (z₀ ∷ c₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-6ᵉ)
  ∷ perm (z₀ ∷ c₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-2-3 : Eqn (₃₊ n)
Rule-CZDD-2-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-7ᵉ)
  ∷ perm (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-2-4 : Eqn (₃₊ n)
Rule-CZDD-2-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (z₀ ∷ c₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-8ᵉ)
  ∷ perm (z₀ ∷ c₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-3-1 : Eqn (₃₊ n)
Rule-CZDD-3-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-9ᵉ)
  ∷ perm (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-3-2 : Eqn (₃₊ n)
Rule-CZDD-3-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  (h₂ ∷ c₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (N-CZDD-3-2)
  ∷ perm (h₂ ∷ c₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-3-3 : Eqn (₃₊ n)
Rule-CZDD-3-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-11ᵉ)
  ∷ perm (h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-3-4 : Eqn (₃₊ n)
Rule-CZDD-3-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  (h₂ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-12ᵉ)
  ∷ perm (h₂ ∷ c₁ ∷ h₂ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-4-1 : Eqn (₃₊ n)
Rule-CZDD-4-1 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-13ᵉ)
  ∷ perm (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-4-2 : Eqn (₃₊ n)
Rule-CZDD-4-2 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (z₀ ∷ c₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-14ᵉ)
  ∷ perm (z₀ ∷ c₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-4-3 : Eqn (₃₊ n)
Rule-CZDD-4-3 = derive
  (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (N-CZDD-4-3)
  ∷ perm (h₁ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl

Rule-CZDD-4-4 : Eqn (₃₊ n)
Rule-CZDD-4-4 = derive
  (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  (z₀ ∷ c₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ( perm (c₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ c₀ ∷ [])
  ∷ rw 0 (T9-16ᵉ)
  ∷ perm (z₀ ∷ c₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ [])
  ∷ [])
  Eq.refl
