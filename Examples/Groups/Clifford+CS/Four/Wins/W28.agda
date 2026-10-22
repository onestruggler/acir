------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the four-wire derivations, each decided once
--
-- Each lemma is one window step of Four/D: two words on three wires with
-- the same operator, equal by completeness on three wires
-- (Windows.win, one evaluation), stated over the macro letters as
-- Four/D uses it.  Written by scratchpad/four/winlib4.py and restated
-- by winmac4.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Wins.W28 where

open import Data.List using ([] ; _∷_)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Windows using (Base ; win)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters

wn01421 : Base 3 → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn01421 b = win 0 3 b (CS • CS • CS • (S ↑) • CK₁₀ • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • (S ↑) • (S ↑) • (S ↑) • (S ↑) • CK₁₀ • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • CS • CS • CS • (S ↑) • CK₁₀ • CS • CS • CS • CS • CS • CS) _ _ Eq.refl
wn01422 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK13⁻ ∷ []) ⟫ʷ
wn01422 b = win 0 3 b (Toffᵗ) ((Swap ↑ • CK₀₁ • Swap ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S • CK₀₁) • Swap ↑)) _ _ Eq.refl
wn01423 : Base 3 → ⟪ (CK13 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CK13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn01423 b = win 0 3 b ((Swap ↑ • CK₀₁ • Swap ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (Toffᵗ) _ _ Eq.refl
wn01424 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn01424 b = win 3 0 b (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01425 : Base 3 → ⟪ (CK10 ∷ CS02 ∷ CK20 ∷ CS02⁻ ∷ CK10⁻ ∷ CS02 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn01425 b = win 3 0 b (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01426 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn01426 b = win 3 0 b (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • (S ↑) • (S ↑) • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) _ _ Eq.refl
wn01427 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn01427 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • CS • (S ↑) • (S ↑) • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01428 : Base 3 → ⟪ (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) ⟫ʷ
wn01428 b = win 3 0 b (CS • CK₁₀ • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • CS • (S ↑ • CK₁₀) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (CS • CS • CK₁₀ • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01429 : Base 3 → ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn01429 b = win 3 0 b (X • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (Swap ↑ • CX₀₁ • Swap ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • X) (X • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • X • X • (Swap ↑ • CX₀₁ • Swap ↑) • X • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • X • (Swap ↑ • CX₀₁ • Swap ↑) • X • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑)) _ _ Eq.refl
wn01430 : Base 3 → ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X0 ∷ X0 ∷ CX02 ∷ X0 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX02 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ CX02 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X0 ∷ []) ⟫ʷ
wn01430 b = win 3 0 b (X • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • X • X • (Swap ↑ • CX₀₁ • Swap ↑) • X • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • X • (Swap ↑ • CX₀₁ • Swap ↑) • X • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑)) (X • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (Swap ↑ • CX₀₁ • Swap ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (S ↑ ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • X) _ _ Eq.refl
wn01431 : Base 3 → ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
wn01431 b = win 3 0 b (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑) • X) (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • CX₀₁ • X • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • X • CX₀₁ • X • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑)) _ _ Eq.refl
wn01432 : Base 3 → ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) ⟫ʷ
wn01432 b = win 3 0 b (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • CX₀₁ • X • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • X • CX₀₁ • X • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑)) (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑) • X) _ _ Eq.refl
wn01433 : Base 3 → ⟪ (CX32 ∷ CS13 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wn01433 b = win 0 3 b ((CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑)) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01434 : Base 3 → ⟪ (CX32 ∷ CS13⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
wn01434 b = win 0 3 b ((CX₁₀ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₁₀ ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01435 : Base 3 → ⟪ (Toff012 ∷ CS02 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ CS02 ∷ []) ⟫ʷ
wn01435 b = win 3 0 b (Toff • (Swap ↑ • CS • Swap ↑) • Toff) ((CS ↑) • CCZ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01436 : Base 3 → ⟪ (CZ13 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01436 b = win 0 3 b ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) _ _ Eq.refl
wn01437 : Base 3 → ⟪ (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn01437 b = win 0 3 b (K • CCZ • (K • iI)) (Toff) _ _ Eq.refl
wn01438 : Base 3 → ⟪ (CS12 ∷ CS12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01438 b = win 3 0 b ((CS ↑) • (CS ↑) • (CZ ↑)) (ε) _ _ Eq.refl
wn01439 : Base 3 → ⟪ (CS02⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01439 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Toff) (Toff • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn01440 : Base 3 → ⟪ (CS12⁻ ∷ CS12⁻ ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01440 b = win 3 0 b (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CZ ↑)) (ε) _ _ Eq.refl
wn01441 : Base 3 → ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ
wn01441 b = win 3 0 b ((X ↑ ↑) • Toff • (X ↑ ↑)) (K • CZ • CCZ • (K • iI)) _ _ Eq.refl
wn01442 : Base 3 → ⟪ (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
wn01442 b = win 3 0 b (K • CZ • CCZ • (K • iI)) ((X ↑ ↑) • Toff • (X ↑ ↑)) _ _ Eq.refl
wn01443 : Base 3 → ⟪ (S0 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn01443 b = win 3 0 b (S • Toff) (Toff • S • (CS ↑) • CCZ) _ _ Eq.refl
wn01444 : Base 3 → ⟪ (CS13⁻ ∷ CS13⁻ ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01444 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) _ _ Eq.refl
wn01445 : Base 3 → ⟪ (S0⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S0⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01445 b = win 3 0 b ((S • S • S) • Toff) (Toff • (S • S • S) • ((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn01446 : Base 3 → ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ
wn01446 b = win 3 0 b ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) (K • Z • CZ • (Swap ↑ • CZ • Swap ↑) • CCZ • (K • iI)) _ _ Eq.refl
wn01447 : Base 3 → ⟪ (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
wn01447 b = win 3 0 b (K • Z • CZ • (Swap ↑ • CZ • Swap ↑) • CCZ • (K • iI)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01448 : Base 3 → ⟪ (K1⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ K1⁻ ∷ []) ⟫ʷ
wn01448 b = win 3 0 b (((K • iI) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn01449 : Base 3 → ⟪ (K1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ K1 ∷ []) ⟫ʷ
wn01449 b = win 3 0 b ((K ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑)) _ _ Eq.refl
wn01450 : Base 3 → ⟪ (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
wn01450 b = win 3 0 b ((K ↑) • CCZ • ((K • iI) ↑)) ((K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01451 : Base 3 → ⟪ (K1⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ K1⁻ ∷ []) ⟫ʷ
wn01451 b = win 3 0 b (((K • iI) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn01452 : Base 3 → ⟪ (K1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ K1 ∷ []) ⟫ʷ
wn01452 b = win 3 0 b ((K ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (K ↑)) _ _ Eq.refl
wn01453 : Base 3 → ⟪ (CZ12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01453 b = win 3 0 b ((CZ ↑) • (CZ ↑)) (ε) _ _ Eq.refl
wn01454 : Base 3 → ⟪ (CS12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
wn01454 b = win 3 0 b ((CS ↑) • (CZ ↑)) (((CS • CS • CS) ↑)) _ _ Eq.refl
wn01455 : Base 3 → ⟪ (CS12 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01455 b = win 3 0 b ((CS ↑) • ((CS • CS • CS) ↑)) (ε) _ _ Eq.refl
wn01456 : Base 3 → ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS02 ∷ K0 ∷ []) ⟫ʷ
wn01456 b = win 3 0 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ((K • iI) • (Swap ↑ • CS • Swap ↑) • K) _ _ Eq.refl
wn01457 : Base 3 → ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS02⁻ ∷ K0 ∷ []) ⟫ʷ
wn01457 b = win 3 0 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ((K • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • K) _ _ Eq.refl
wn01458 : Base 3 → ⟪ (Toff012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn01458 b = win 3 0 b (Toff • (K • iI)) ((K • iI) • CCZ) _ _ Eq.refl
wn01459 : Base 3 → ⟪ (CK20 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01459 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑)) (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01460 : Base 3 → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
wn01460 b = win 3 0 b (K) (K) _ _ Eq.refl
wn01461 : Base 3 → ⟪ (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
wn01461 b = win 3 0 b (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01462 : Base 3 → ⟪ (CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01462 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01463 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ []) ⟫ʷ
wn01463 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01464 : Base 3 → ⟪ (CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01464 b = win 3 0 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01465 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ []) ⟫ʷ
wn01465 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn01466 : Base 3 → ⟪ (CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01466 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01467 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01467 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01468 : Base 3 → ⟪ (S1 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ S1 ∷ CS23 ∷ CCZ123 ∷ []) ⟫ʷ
wn01468 b = win 0 3 b (S • Toff) (Toff • S • (CS ↑) • CCZ) _ _ Eq.refl
wn01469 : Base 3 → ⟪ (CCZ123 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ
wn01469 b = win 0 3 b (CCZ • Toff) (Toff • (CZ ↑) • CCZ) _ _ Eq.refl
wn01470 : Base 3 → ⟪ (CS23 ∷ CS23 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01470 b = win 0 3 b ((CS ↑) • (CS ↑) • (CZ ↑)) (ε) _ _ Eq.refl
wn01471 : Base 3 → ⟪ (CS13⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS13⁻ ∷ CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn01471 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Toff) (Toff • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn01472 : Base 3 → ⟪ (CS23⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS23⁻ ∷ []) ⟫ʷ
wn01472 b = win 0 3 b (((CS • CS • CS) ↑) • Toff) (Toff • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn01473 : Base 3 → ⟪ (CS23⁻ ∷ CS23⁻ ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01473 b = win 0 3 b (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CZ ↑)) (ε) _ _ Eq.refl
wn01474 : Base 3 → ⟪ (CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01474 b = win 3 0 b ((CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01475 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ []) ⟫ʷ
wn01475 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn01476 : Base 3 → ⟪ (CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01476 b = win 3 0 b ((CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01477 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ []) ⟫ʷ
wn01477 b = win 3 0 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑)) _ _ Eq.refl
wn01478 : Base 3 → ⟪ (CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01478 b = win 3 0 b (((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01479 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ []) ⟫ʷ
wn01479 b = win 3 0 b ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn01480 : Base 3 → ⟪ (CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01480 b = win 3 0 b (((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01481 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ []) ⟫ʷ
wn01481 b = win 3 0 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn01482 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01482 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01483 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01483 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01484 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn01484 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01485 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01485 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01486 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01486 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01487 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01487 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01488 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01488 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01489 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01489 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01490 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01490 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01491 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01491 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01492 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn01492 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01493 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01493 b = win 0 3 b ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn01494 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01494 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01495 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01495 b = win 0 3 b ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn01496 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01496 b = win 3 0 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01497 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01497 b = win 0 3 b ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn01498 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01498 b = win 3 0 b ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01499 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01499 b = win 0 3 b ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn01500 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01500 b = win 3 0 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01501 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01501 b = win 3 0 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01502 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01502 b = win 3 0 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01503 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01503 b = win 3 0 b ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01504 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01504 b = win 3 0 b ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01505 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01505 b = win 3 0 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01506 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn01506 b = win 3 0 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01507 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01507 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01508 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01508 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01509 : Base 3 → ⟪ (K1⁻ ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01509 b = win 3 0 b (((K • iI) ↑) • (K ↑)) (ε) _ _ Eq.refl
wn01510 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K1⁻ ∷ K1 ∷ []) ⟫ʷ
wn01510 b = win 3 0 b (ε) (((K • iI) ↑) • (K ↑)) _ _ Eq.refl
wn01511 : Base 3 → ⟪ (CS12 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn01511 b = win 3 0 b ((CS ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) _ _ Eq.refl
