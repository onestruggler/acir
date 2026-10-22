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

module Examples.Groups.Clifford+CS.Four.Wins.W48 where

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

wn02437 : Base 3 → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) ⟫ʷ
wn02437 b = win 0 3 b (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn02438 : Base 3 → ⟪ (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
wn02438 b = win 0 3 b (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02439 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02439 b = win 3 0 b ((X ↑) • CS • (X ↑) • S • (K • iI) • (S • S • S)) (S • (K • iI) • (S • S • S) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02440 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02440 b = win 3 0 b ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • S • K • (S • S • S)) (S • K • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02441 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02441 b = win 3 0 b ((K • iI) • (K • iI) • (S • S • S)) ((S • S • S) • (K • iI) • (K • iI)) _ _ Eq.refl
wn02442 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02442 b = win 3 0 b (S • K) (K • K • S • (K • iI)) _ _ Eq.refl
wn02443 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02443 b = win 3 0 b ((X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02444 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02444 b = win 3 0 b ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • K • K • K) (K • K • K • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02445 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02445 b = win 3 0 b ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) ((S • S • S) • (K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02446 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02446 b = win 3 0 b ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • K • K • S) (K • K • K • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02447 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02447 b = win 3 0 b (S • S • (K • iI) • S) (S • S • (K • iI) • S) _ _ Eq.refl
wn02448 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02448 b = win 3 0 b ((S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • S) _ _ Eq.refl
wn02449 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02449 b = win 3 0 b ((K • iI) • S • S • K • S) ((S • S • S) • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02450 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02450 b = win 3 0 b ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • S • (K • iI)) _ _ Eq.refl
wn02451 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02451 b = win 3 0 b ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • S • (K • iI)) ((S • S • S) • (K • iI) • S • S • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02452 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02452 b = win 3 0 b ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • S • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02453 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02453 b = win 3 0 b ((X ↑) • CK₁₀ • (X ↑) • S • S • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02454 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02454 b = win 3 0 b ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02455 : Base 3 → ⟪ (S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02455 b = win 3 0 b (S • S • S • K • S • S) ((S • S • S) • K • S • S) _ _ Eq.refl
wn02456 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02456 b = win 3 0 b ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • S • S) _ _ Eq.refl
wn02457 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02457 b = win 3 0 b ((X ↑) • CS • (X ↑) • S • K • (S • S • S) • K • K) (S • K • (S • S • S) • K • K • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02458 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02458 b = win 3 0 b ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02459 : Base 3 → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02459 b = win 3 0 b ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • K • K) (K • (S • S • S) • K • K • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02460 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02460 b = win 3 0 b ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02461 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02461 b = win 3 0 b ((S • S • S) • S • S • (K • iI)) (S • (K • iI)) _ _ Eq.refl
wn02462 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02462 b = win 3 0 b (K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02463 : Base 3 → ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02463 b = win 3 0 b (K • S • S • K • K • K • K) (S • (K • iI) • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02464 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02464 b = win 3 0 b ((K • iI) • (K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) (S • K • (S • S • S) • K • (S • S • S) • K) _ _ Eq.refl
wn02465 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02465 b = win 3 0 b ((S • S • S) • (S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) (S • S • (K • iI) • S • (K • iI) • (K • iI)) _ _ Eq.refl
wn02466 : Base 3 → ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02466 b = win 3 0 b (K • K • (S • S • S) • K • S) (K • K • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02467 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02467 b = win 3 0 b ((K • iI) • S • S • (K • iI) • S • (K • iI) • (K • iI)) ((S • S • S) • K • S • S • K) _ _ Eq.refl
wn02468 : Base 3 → ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02468 b = win 3 0 b (K • K • (S • S • S) • K • (S • S • S) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S • (K • iI)) _ _ Eq.refl
wn02469 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02469 b = win 3 0 b ((S • S • S) • S • S • K • K • K) (S • K • K • K) _ _ Eq.refl
wn02470 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02470 b = win 3 0 b ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02471 : Base 3 → ⟪ (K0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02471 b = win 3 0 b (K • S • K • K • K) ((S • S • S) • K • (S • S • S) • K • K) _ _ Eq.refl
wn02472 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02472 b = win 3 0 b ((K • iI) • (K • iI) • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • S • K) _ _ Eq.refl
wn02473 : Base 3 → ⟪ (CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ
wn02473 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02474 : Base 3 → ⟪ (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) ⟫ʷ
wn02474 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02475 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02475 b = win 3 0 b (S • K) ((S • S • S) • (K • iI) • (S • S • S) • S • K • S • S • K) _ _ Eq.refl
wn02476 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn02476 b = win 3 0 b ((K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • K • S) _ _ Eq.refl
wn02477 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02477 b = win 3 0 b (S • K • S • S • K) (X • S • S • S) _ _ Eq.refl
wn02478 : Base 3 → ⟪ (S0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02478 b = win 3 0 b (S • S • S • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (X) _ _ Eq.refl
wn02479 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02479 b = win 3 0 b (S • K) ((S • S • S) • K • S • S • S • S • K • S • S • (K • iI)) _ _ Eq.refl
wn02480 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02480 b = win 3 0 b ((K • iI) • (S • S • S)) (K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (S • S • S) • (S • S • S) • (K • iI) • S) _ _ Eq.refl
wn02481 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ ι ∷ ι ∷ []) ⟫ʷ
wn02481 b = win 3 0 b (S • S • K • S • S • (K • iI)) (X • S • S • iI • iI) _ _ Eq.refl
wn02482 : Base 3 → ⟪ (S0 ∷ S0 ∷ ι ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02482 b = win 3 0 b (S • S • iI • iI • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (X) _ _ Eq.refl
wn02483 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02483 b = win 3 0 b (ε) (K • S • S • K • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02484 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02484 b = win 3 0 b (ε) (K • (S • S • S) • (S • S • S) • K • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02485 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ ι ∷ []) ⟫ʷ
wn02485 b = win 3 0 b ((K • iI) • S • S • (K • iI)) (X • iI) _ _ Eq.refl
wn02486 : Base 3 → ⟪ (ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02486 b = win 3 0 b (iI • K • (S • S • S) • (S • S • S) • K) (X) _ _ Eq.refl
wn02487 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02487 b = win 3 0 b ((S • S • S) • S) (ε) _ _ Eq.refl
wn02488 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02488 b = win 3 0 b (ε) (S • S • K • S • S • K • S • S • K • S • S • K) _ _ Eq.refl
wn02489 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02489 b = win 3 0 b (ε) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02490 : Base 3 → ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ ι ∷ []) ⟫ʷ
wn02490 b = win 3 0 b (S • S • K • S • S • K) (X • S • S • iI) _ _ Eq.refl
wn02491 : Base 3 → ⟪ (S0 ∷ S0 ∷ ι ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02491 b = win 3 0 b (S • S • iI • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (X) _ _ Eq.refl
wn02492 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02492 b = win 3 0 b ((S • S • S) • (K • iI) • S • S) (S • K • S • S • K • S • S • K) _ _ Eq.refl
wn02493 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02493 b = win 3 0 b ((S • S • S) • (S • S • S) • K • S) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02494 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02494 b = win 3 0 b ((K • iI) • (S • S • S) • S • K) (ε) _ _ Eq.refl
wn02495 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02495 b = win 3 0 b ((S • S • S) • K) (S • K • K • S • S • (K • iI)) _ _ Eq.refl
wn02496 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02496 b = win 3 0 b ((K • iI) • S) (K • (S • S • S) • (S • S • S) • (K • iI) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02497 : Base 3 → ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02497 b = win 3 0 b (K • S • S • (K • iI)) (X) _ _ Eq.refl
wn02498 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02498 b = win 3 0 b (K • (S • S • S) • (S • S • S) • (K • iI)) (X) _ _ Eq.refl
wn02499 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ
wn02499 b = win 3 0 b (S • K) ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • CS • CK₁₀) _ _ Eq.refl
wn02500 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS01⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02500 b = win 3 0 b ((K • iI) • (S • S • S)) ((S ↑ • CK₁₀) • (CS • CS • CS) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02501 : Base 3 → ⟪ (CS01 ∷ CK10 ∷ CK10⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02501 b = win 3 0 b (CS • CK₁₀ • (S ↑ • CK₁₀) • (CS • CS • CS)) (ε) _ _ Eq.refl
wn02502 : Base 3 → ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) ⟫ʷ
wn02502 b = win 0 3 b (Toff) ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn02503 : Base 3 → ⟪ (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn02503 b = win 0 3 b ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (Toff) _ _ Eq.refl
wn02504 : Base 3 → ⟪ (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ []) ⟫ʷ
wn02504 b = win 3 0 b ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn02505 : Base 3 → ⟪ (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn02505 b = win 3 0 b ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02506 : Base 3 → ⟪ (CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02506 b = win 3 0 b ((CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑)) (ε) _ _ Eq.refl
wn02507 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) ⟫ʷ
wn02507 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02508 : Base 3 → ⟪ (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02508 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) _ _ Eq.refl
wn02509 : Base 3 → ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
wn02509 b = win 0 3 b ((S • S • S) • (K • iI) • S • S) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02510 : Base 3 → ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02510 b = win 0 3 b ((S • S • S) • (S • S • S) • K • S) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02511 : Base 3 → ⟪ (CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02511 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn02512 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02512 b = win 3 0 b ((S • S • S) • S • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02513 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02513 b = win 3 0 b (S • K • (S • S • S)) (S • K • (S • S • S)) _ _ Eq.refl
wn02514 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02514 b = win 3 0 b ((S • S • S) • (K • iI) • (K • iI) • (K • iI)) ((S • S • S) • (K • iI) • (K • iI) • (K • iI)) _ _ Eq.refl
wn02515 : Base 3 → ⟪ (K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02515 b = win 3 0 b (K • K • K) (K • K • K • S • (S • S • S)) _ _ Eq.refl
wn02516 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02516 b = win 3 0 b (K • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) (S • (K • iI) • S) _ _ Eq.refl
wn02517 : Base 3 → ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02517 b = win 3 0 b (K • K • K • S) ((S • S • S) • K • (S • S • S) • K) _ _ Eq.refl
wn02518 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02518 b = win 3 0 b ((S • S • S) • (S • S • S) • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02519 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02519 b = win 3 0 b (K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02520 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02520 b = win 3 0 b ((K • iI) • S • S • (K • iI) • S • S • (K • iI)) (S • S • K • S • S) _ _ Eq.refl
wn02521 : Base 3 → ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02521 b = win 3 0 b (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02522 : Base 3 → ⟪ (S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02522 b = win 3 0 b ((S • S • S) • S • K • (S • S • S) • K • K) (K • (S • S • S) • K • K) _ _ Eq.refl
wn02523 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02523 b = win 3 0 b ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02524 : Base 3 → ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02524 b = win 3 0 b (K • K • (S • S • S) • K • K) ((S • S • S) • K • K • K • K) _ _ Eq.refl
wn02525 : Base 3 → ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02525 b = win 3 0 b ((K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • K) _ _ Eq.refl
wn02526 : Base 3 → ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02526 b = win 3 0 b (S • (K • iI) • S • S • (K • iI) • S) (S • (K • iI) • S • S • (K • iI) • S) _ _ Eq.refl
wn02527 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02527 b = win 3 0 b ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) _ _ Eq.refl
wn02528 : Base 3 → ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ ι ∷ ι ∷ []) ⟫ʷ
wn02528 b = win 3 0 b (S • (K • iI) • S • S • (K • iI) • S) (X • iI • iI) _ _ Eq.refl
wn02529 : Base 3 → ⟪ (ι ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02529 b = win 3 0 b (iI • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) (X) _ _ Eq.refl
wn02530 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02530 b = win 3 0 b ((S • S • S) • (K • iI) • S • S) (S • (K • iI) • (S • S • S) • (K • iI) • S • S • (K • iI) • S) _ _ Eq.refl
wn02531 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02531 b = win 3 0 b ((S • S • S) • (S • S • S) • K • S) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • S • K • (S • S • S)) _ _ Eq.refl
wn02532 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ ι ∷ []) ⟫ʷ
wn02532 b = win 3 0 b ((K • iI) • S • S • (K • iI) • S) (X • S • iI) _ _ Eq.refl
wn02533 : Base 3 → ⟪ (S0 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02533 b = win 3 0 b (S • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K) (X) _ _ Eq.refl
wn02534 : Base 3 → ⟪ (X0 ∷ X1 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02534 b = win 3 0 b (X • (X ↑) • X • (X ↑)) (ε) _ _ Eq.refl
wn02535 : Base 3 → ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ
wn02535 b = win 3 0 b ((X ↑) • (Swap ↑)) ((Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02536 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02536 b = win 3 0 b ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02537 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02537 b = win 3 0 b (S • K • S • S) (S • K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02538 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02538 b = win 3 0 b ((S • S • S) • (S • S • S) • (K • iI) • S • K • S • S • K) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02539 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02539 b = win 3 0 b ((K • iI) • (S • S • S) • (S • S • S) • (K • iI)) (S • K • (S • S • S) • (S • S • S) • (K • iI) • S) _ _ Eq.refl
wn02540 : Base 3 → ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02540 b = win 3 0 b ((S • S • S) • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • S • S) _ _ Eq.refl
wn02541 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02541 b = win 3 0 b (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • S) ((S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02542 : Base 3 → ⟪ (S0 ∷ K0 ∷ CCZ012 ∷ CS12⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ
wn02542 b = win 3 0 b (S • K • CCZ • ((CS • CS • CS) ↑) • (K • iI) • (S • S • S)) (((CS • CS • CS) ↑) • S • Toff • (S • S • S)) _ _ Eq.refl
wn02543 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ
wn02543 b = win 3 0 b (S • K • S • (S • S • S)) (S • K) _ _ Eq.refl
wn02544 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02544 b = win 3 0 b ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • S • K • S • S • K) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02545 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02545 b = win 3 0 b ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (S • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02546 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02546 b = win 3 0 b (S • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) ((K • iI) • S • S) _ _ Eq.refl
wn02547 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02547 b = win 3 0 b (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) ((S • S • S) • (S • S • S) • K) _ _ Eq.refl
wn02548 : Base 3 → ⟪ (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CX10 ∷ []) ⟫ʷ
wn02548 b = win 3 0 b (S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑) • S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑)) (CZ • CX₁₀) _ _ Eq.refl
wn02549 : Base 3 → ⟪ (S1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S0⁻ ∷ []) ⟫ʷ
wn02549 b = win 3 0 b (((S • S • S) ↑) • Swap) (Swap • (S • S • S)) _ _ Eq.refl
wn02550 : Base 3 → ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn02550 b = win 3 0 b (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn02551 : Base 3 → ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02551 b = win 3 0 b (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02552 : Base 3 → ⟪ (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02552 b = win 3 0 b (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) (ε) _ _ Eq.refl
wn02553 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02553 b = win 3 0 b ((S • S • S) • (K • iI) • S • S) ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS) _ _ Eq.refl
wn02554 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02554 b = win 3 0 b ((S • S • S) • (S • S • S) • K • S) ((CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02555 : Base 3 → ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02555 b = win 3 0 b ((CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS • (CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS) (ε) _ _ Eq.refl
wn02556 : Base 3 → ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) ⟫ʷ
wn02556 b = win 0 3 b (Toff) (CK₁₀ • CCZ • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02557 : Base 3 → ⟪ (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn02557 b = win 0 3 b (CK₁₀ • CCZ • (S ↑ • CK₁₀)) (Toff) _ _ Eq.refl
wn02558 : Base 3 → ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02558 b = win 3 0 b ((S • S • S) • (S • S • S) • K • S • (S • S • S) • (K • iI) • S • S) (ε) _ _ Eq.refl
wn02559 : Base 3 → ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ
wn02559 b = win 0 3 b (((CS • CS • CS) ↑) • CCZ) (CCZ • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn02560 : Base 3 → ⟪ (Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
wn02560 b = win 0 3 b (Swap • Swap • (Swap ↑) • Swap) (Swap • (Swap ↑) • Swap • (Swap ↑)) _ _ Eq.refl
wn02561 : Base 3 → ⟪ (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CZ01 ∷ []) ⟫ʷ
wn02561 b = win 3 0 b (((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑)) (CX₁₀ • CZ) _ _ Eq.refl
wn02562 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CZ01 ∷ CZ01 ∷ []) ⟫ʷ
wn02562 b = win 3 0 b (ε) (CZ • CZ) _ _ Eq.refl
wn02563 : Base 3 → ⟪ (CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02563 b = win 3 0 b (CZ) (CS • CS) _ _ Eq.refl
wn02564 : Base 3 → ⟪ (CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn02564 b = win 3 0 b (CZ) ((CS • CS • CS) • (CS • CS • CS)) _ _ Eq.refl
wn02565 : Base 3 → ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CZ01 ∷ X0 ∷ []) ⟫ʷ
wn02565 b = win 3 0 b ((S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑)) (X • CX₁₀ • CZ • X) _ _ Eq.refl
wn02566 : Base 3 → ⟪ (X2 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wn02566 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (X ↑)) (S) _ _ Eq.refl
wn02567 : Base 3 → ⟪ (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
wn02567 b = win 3 0 b (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ) ((S ↑)) _ _ Eq.refl
wn02568 : Base 3 → ⟪ (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
wn02568 b = win 3 0 b ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ • X • (X ↑)) ((S ↑ ↑)) _ _ Eq.refl
wn02569 : Base 3 → ⟪ (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wn02569 b = win 3 0 b (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • X • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) (CS) _ _ Eq.refl
wn02570 : Base 3 → ⟪ (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn02570 b = win 3 0 b ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) ((CS ↑)) _ _ Eq.refl
wn02571 : Base 3 → ⟪ (CS23 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
wn02571 b = win 0 3 b ((CS ↑) • CCZ • CCZ) ((CS ↑)) _ _ Eq.refl
