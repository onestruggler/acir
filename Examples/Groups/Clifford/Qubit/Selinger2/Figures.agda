------------------------------------------------------------------------
-- Presentations of groups
--
-- Selinger's Figures 3-7, replayed from the supplement (GENERATED).
--
-- This file is produced by local/tools/emit.py from the machine-readable
-- proof file of arXiv:1310.6813; do not edit it by hand.
--
-- This first instalment is the 10 equations every step of which is
-- (def), i.e. that hold by unfolding the box definitions of Definition
-- 4.2 alone.  Boxes A₁, C₁ and E₁ unfold to ε, and to-list drops those,
-- so by-assoc closes each one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger2.Figures where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (ε ; _•_ ; _^_)
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford.Qubit.Selinger2.Figure8
open import Examples.Groups.Clifford.Qubit.Selinger2.Boxes

private
  module A {k : ℕ} = Assoc (k CRel,_===_)

-- Equation 3.1
eq-3-1 : ∀ {n} → _≈ᶠ_ {₁₊ n} (ε) ([ a₁ ]ᴬ • [ c₁ ]ᶜ • [ e₁ ]ᴱ)
eq-3-1 = A.by-assoc Eq.refl

-- Equation 3.3
eq-3-3 : ∀ {n} → _≈ᶠ_ {₁₊ n} (H • [ a₁ ]ᴬ) ([ a₂ ]ᴬ)
eq-3-3 = A.by-assoc Eq.refl

-- Equation 3.6
eq-3-6 : ∀ {n} → _≈ᶠ_ {₁₊ n} (S • [ a₁ ]ᴬ) ([ a₁ ]ᴬ • S)
eq-3-6 = A.by-assoc Eq.refl

-- Equation 3.9
eq-3-9 : ∀ {n} → _≈ᶠ_ {₂₊ n} (CZ • [ a₁ ]ᴬ) ([ a₁ ]ᴬ • CZ)
eq-3-9 = A.by-assoc Eq.refl

-- Equation 3.44
eq-3-44 : ∀ {n} → _≈ᶠ_ {₁₊ n} (X • [ c₁ ]ᶜ) ([ c₂ ]ᶜ)
eq-3-44 = A.by-assoc Eq.refl

-- Equation 3.46
eq-3-46 : ∀ {n} → _≈ᶠ_ {₁₊ n} (S • [ c₁ ]ᶜ) ([ c₁ ]ᶜ • S)
eq-3-46 = A.by-assoc Eq.refl

-- Equation 3.48
eq-3-48 : ∀ {n} → _≈ᶠ_ {₂₊ n} (CZ • [ c₁ ]ᶜ) ([ c₁ ]ᶜ • CZ)
eq-3-48 = A.by-assoc Eq.refl

-- Equation 3.82
eq-3-82 : ∀ {n} → _≈ᶠ_ {₁₊ n} (S • [ e₁ ]ᴱ) ([ e₂ ]ᴱ)
eq-3-82 = A.by-assoc Eq.refl

-- Equation 3.83
eq-3-83 : ∀ {n} → _≈ᶠ_ {₁₊ n} (S • [ e₂ ]ᴱ) ([ e₃ ]ᴱ)
eq-3-83 = A.by-assoc Eq.refl

-- Equation 3.84
eq-3-84 : ∀ {n} → _≈ᶠ_ {₁₊ n} (S • [ e₃ ]ᴱ) ([ e₄ ]ᴱ)
eq-3-84 = A.by-assoc Eq.refl

