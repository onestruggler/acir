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
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn02437 : ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) ⟫ʷ
wn02437 = win 0 3 complete₃ (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn02438 : ⟪ (CS12 ∷ CK31 ∷ CS12⁻ ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
wn02438 = win 0 3 complete₃ (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02439 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02439 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • (K • iI) • (S • S • S)) (S • (K • iI) • (S • S • S) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02440 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02440 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • S • K • (S • S • S)) (S • K • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02441 : ⟪ (K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02441 = win 3 0 complete₃ ((K • iI) • (K • iI) • (S • S • S)) ((S • S • S) • (K • iI) • (K • iI)) _ _ Eq.refl
wn02442 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02442 = win 3 0 complete₃ (S • K) (K • K • S • (K • iI)) _ _ Eq.refl
wn02443 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02443 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02444 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02444 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • K • K • K) (K • K • K • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02445 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02445 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) ((S • S • S) • (K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02446 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02446 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • K • K • S) (K • K • K • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02447 : ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02447 = win 3 0 complete₃ (S • S • (K • iI) • S) (S • S • (K • iI) • S) _ _ Eq.refl
wn02448 : ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02448 = win 3 0 complete₃ ((S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • S) _ _ Eq.refl
wn02449 : ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02449 = win 3 0 complete₃ ((K • iI) • S • S • K • S) ((S • S • S) • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02450 : ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02450 = win 3 0 complete₃ ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • S • (K • iI)) _ _ Eq.refl
wn02451 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02451 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • S • (K • iI)) ((S • S • S) • (K • iI) • S • S • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02452 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02452 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • S • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02453 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02453 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • S • S • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02454 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02454 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02455 : ⟪ (S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02455 = win 3 0 complete₃ (S • S • S • K • S • S) ((S • S • S) • K • S • S) _ _ Eq.refl
wn02456 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02456 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • S • S) _ _ Eq.refl
wn02457 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02457 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • K • (S • S • S) • K • K) (S • K • (S • S • S) • K • K • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02458 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02458 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02459 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02459 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • K • K) (K • (S • S • S) • K • K • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02460 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02460 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02461 : ⟪ (S0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02461 = win 3 0 complete₃ ((S • S • S) • S • S • (K • iI)) (S • (K • iI)) _ _ Eq.refl
wn02462 : ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02462 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02463 : ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02463 = win 3 0 complete₃ (K • S • S • K • K • K • K) (S • (K • iI) • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02464 : ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02464 = win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) (S • K • (S • S • S) • K • (S • S • S) • K) _ _ Eq.refl
wn02465 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02465 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) (S • S • (K • iI) • S • (K • iI) • (K • iI)) _ _ Eq.refl
wn02466 : ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02466 = win 3 0 complete₃ (K • K • (S • S • S) • K • S) (K • K • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02467 : ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02467 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI) • S • (K • iI) • (K • iI)) ((S • S • S) • K • S • S • K) _ _ Eq.refl
wn02468 : ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02468 = win 3 0 complete₃ (K • K • (S • S • S) • K • (S • S • S) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S • (K • iI)) _ _ Eq.refl
wn02469 : ⟪ (S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02469 = win 3 0 complete₃ ((S • S • S) • S • S • K • K • K) (S • K • K • K) _ _ Eq.refl
wn02470 : ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02470 = win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02471 : ⟪ (K0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02471 = win 3 0 complete₃ (K • S • K • K • K) ((S • S • S) • K • (S • S • S) • K • K) _ _ Eq.refl
wn02472 : ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02472 = win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • S • K) _ _ Eq.refl
wn02473 : ⟪ (CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ
wn02473 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02474 : ⟪ (CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ []) ⟫ʷ
wn02474 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02475 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02475 = win 3 0 complete₃ (S • K) ((S • S • S) • (K • iI) • (S • S • S) • S • K • S • S • K) _ _ Eq.refl
wn02476 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn02476 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • K • S) _ _ Eq.refl
wn02477 : ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02477 = win 3 0 complete₃ (S • K • S • S • K) (X • S • S • S) _ _ Eq.refl
wn02478 : ⟪ (S0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02478 = win 3 0 complete₃ (S • S • S • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (X) _ _ Eq.refl
wn02479 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02479 = win 3 0 complete₃ (S • K) ((S • S • S) • K • S • S • S • S • K • S • S • (K • iI)) _ _ Eq.refl
wn02480 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02480 = win 3 0 complete₃ ((K • iI) • (S • S • S)) (K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (S • S • S) • (S • S • S) • (K • iI) • S) _ _ Eq.refl
wn02481 : ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ ι ∷ ι ∷ []) ⟫ʷ
wn02481 = win 3 0 complete₃ (S • S • K • S • S • (K • iI)) (X • S • S • iI • iI) _ _ Eq.refl
wn02482 : ⟪ (S0 ∷ S0 ∷ ι ∷ ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02482 = win 3 0 complete₃ (S • S • iI • iI • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (X) _ _ Eq.refl
wn02483 : ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02483 = win 3 0 complete₃ (ε) (K • S • S • K • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02484 : ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02484 = win 3 0 complete₃ (ε) (K • (S • S • S) • (S • S • S) • K • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02485 : ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ ι ∷ []) ⟫ʷ
wn02485 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI)) (X • iI) _ _ Eq.refl
wn02486 : ⟪ (ι ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02486 = win 3 0 complete₃ (iI • K • (S • S • S) • (S • S • S) • K) (X) _ _ Eq.refl
wn02487 : ⟪ (S0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02487 = win 3 0 complete₃ ((S • S • S) • S) (ε) _ _ Eq.refl
wn02488 : ⟪ [] ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02488 = win 3 0 complete₃ (ε) (S • S • K • S • S • K • S • S • K • S • S • K) _ _ Eq.refl
wn02489 : ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02489 = win 3 0 complete₃ (ε) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02490 : ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ S0 ∷ ι ∷ []) ⟫ʷ
wn02490 = win 3 0 complete₃ (S • S • K • S • S • K) (X • S • S • iI) _ _ Eq.refl
wn02491 : ⟪ (S0 ∷ S0 ∷ ι ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02491 = win 3 0 complete₃ (S • S • iI • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (X) _ _ Eq.refl
wn02492 : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02492 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) (S • K • S • S • K • S • S • K) _ _ Eq.refl
wn02493 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02493 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02494 : ⟪ (K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02494 = win 3 0 complete₃ ((K • iI) • (S • S • S) • S • K) (ε) _ _ Eq.refl
wn02495 : ⟪ (S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02495 = win 3 0 complete₃ ((S • S • S) • K) (S • K • K • S • S • (K • iI)) _ _ Eq.refl
wn02496 : ⟪ (K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02496 = win 3 0 complete₃ ((K • iI) • S) (K • (S • S • S) • (S • S • S) • (K • iI) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02497 : ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02497 = win 3 0 complete₃ (K • S • S • (K • iI)) (X) _ _ Eq.refl
wn02498 : ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02498 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • (K • iI)) (X) _ _ Eq.refl
wn02499 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ
wn02499 = win 3 0 complete₃ (S • K) ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • CS • CK₁₀) _ _ Eq.refl
wn02500 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS01⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02500 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((S ↑ • CK₁₀) • (CS • CS • CS) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02501 : ⟪ (CS01 ∷ CK10 ∷ CK10⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02501 = win 3 0 complete₃ (CS • CK₁₀ • (S ↑ • CK₁₀) • (CS • CS • CS)) (ε) _ _ Eq.refl
wn02502 : ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) ⟫ʷ
wn02502 = win 0 3 complete₃ (Toff) ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn02503 : ⟪ (CK31 ∷ CCZ123 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn02503 = win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (Toff) _ _ Eq.refl
wn02504 : ⟪ (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ []) ⟫ʷ
wn02504 = win 3 0 complete₃ ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn02505 : ⟪ (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn02505 = win 3 0 complete₃ ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02506 : ⟪ (CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02506 = win 3 0 complete₃ ((CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑)) (ε) _ _ Eq.refl
wn02507 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) ⟫ʷ
wn02507 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02508 : ⟪ (CS02 ∷ CK10 ∷ CS02⁻ ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02508 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) _ _ Eq.refl
wn02509 : ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ []) ⟫ʷ
wn02509 = win 0 3 complete₃ ((S • S • S) • (K • iI) • S • S) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02510 : ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02510 = win 0 3 complete₃ ((S • S • S) • (S • S • S) • K • S) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02511 : ⟪ (CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02511 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn02512 : ⟪ (S0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02512 = win 3 0 complete₃ ((S • S • S) • S • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02513 : ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02513 = win 3 0 complete₃ (S • K • (S • S • S)) (S • K • (S • S • S)) _ _ Eq.refl
wn02514 : ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02514 = win 3 0 complete₃ ((S • S • S) • (K • iI) • (K • iI) • (K • iI)) ((S • S • S) • (K • iI) • (K • iI) • (K • iI)) _ _ Eq.refl
wn02515 : ⟪ (K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02515 = win 3 0 complete₃ (K • K • K) (K • K • K • S • (S • S • S)) _ _ Eq.refl
wn02516 : ⟪ (K0 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02516 = win 3 0 complete₃ (K • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) (S • (K • iI) • S) _ _ Eq.refl
wn02517 : ⟪ (K0 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02517 = win 3 0 complete₃ (K • K • K • S) ((S • S • S) • K • (S • S • S) • K) _ _ Eq.refl
wn02518 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02518 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02519 : ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02519 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02520 : ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02520 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI) • S • S • (K • iI)) (S • S • K • S • S) _ _ Eq.refl
wn02521 : ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02521 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02522 : ⟪ (S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02522 = win 3 0 complete₃ ((S • S • S) • S • K • (S • S • S) • K • K) (K • (S • S • S) • K • K) _ _ Eq.refl
wn02523 : ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02523 = win 3 0 complete₃ ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02524 : ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02524 = win 3 0 complete₃ (K • K • (S • S • S) • K • K) ((S • S • S) • K • K • K • K) _ _ Eq.refl
wn02525 : ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02525 = win 3 0 complete₃ ((K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • K) _ _ Eq.refl
wn02526 : ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02526 = win 3 0 complete₃ (S • (K • iI) • S • S • (K • iI) • S) (S • (K • iI) • S • S • (K • iI) • S) _ _ Eq.refl
wn02527 : ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02527 = win 3 0 complete₃ ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) _ _ Eq.refl
wn02528 : ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ ι ∷ ι ∷ []) ⟫ʷ
wn02528 = win 3 0 complete₃ (S • (K • iI) • S • S • (K • iI) • S) (X • iI • iI) _ _ Eq.refl
wn02529 : ⟪ (ι ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02529 = win 3 0 complete₃ (iI • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) (X) _ _ Eq.refl
wn02530 : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02530 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) (S • (K • iI) • (S • S • S) • (K • iI) • S • S • (K • iI) • S) _ _ Eq.refl
wn02531 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn02531 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • S • K • (S • S • S)) _ _ Eq.refl
wn02532 : ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ ι ∷ []) ⟫ʷ
wn02532 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI) • S) (X • S • iI) _ _ Eq.refl
wn02533 : ⟪ (S0 ∷ ι ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02533 = win 3 0 complete₃ (S • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K) (X) _ _ Eq.refl
wn02534 : ⟪ (X0 ∷ X1 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02534 = win 3 0 complete₃ (X • (X ↑) • X • (X ↑)) (ε) _ _ Eq.refl
wn02535 : ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ
wn02535 = win 3 0 complete₃ ((X ↑) • (Swap ↑)) ((Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02536 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02536 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02537 : ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02537 = win 3 0 complete₃ (S • K • S • S) (S • K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02538 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02538 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • K • S • S • K) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02539 : ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02539 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S) • (K • iI)) (S • K • (S • S • S) • (S • S • S) • (K • iI) • S) _ _ Eq.refl
wn02540 : ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02540 = win 3 0 complete₃ ((S • S • S) • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • S • S) _ _ Eq.refl
wn02541 : ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02541 = win 3 0 complete₃ (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • S) ((S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02542 : ⟪ (S0 ∷ K0 ∷ CCZ012 ∷ CS12⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ
wn02542 = win 3 0 complete₃ (S • K • CCZ • ((CS • CS • CS) ↑) • (K • iI) • (S • S • S)) (((CS • CS • CS) ↑) • S • Toff • (S • S • S)) _ _ Eq.refl
wn02543 : ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ
wn02543 = win 3 0 complete₃ (S • K • S • (S • S • S)) (S • K) _ _ Eq.refl
wn02544 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02544 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • S • K • S • S • K) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02545 : ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02545 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (S • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02546 : ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02546 = win 3 0 complete₃ (S • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) ((K • iI) • S • S) _ _ Eq.refl
wn02547 : ⟪ (S0 ∷ K0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02547 = win 3 0 complete₃ (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) ((S • S • S) • (S • S • S) • K) _ _ Eq.refl
wn02548 : ⟪ (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CX10 ∷ []) ⟫ʷ
wn02548 = win 3 0 complete₃ (S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑) • S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑)) (CZ • CX₁₀) _ _ Eq.refl
wn02549 : ⟪ (S1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S0⁻ ∷ []) ⟫ʷ
wn02549 = win 3 0 complete₃ (((S • S • S) ↑) • Swap) (Swap • (S • S • S)) _ _ Eq.refl
wn02550 : ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn02550 = win 3 0 complete₃ (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn02551 : ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02551 = win 3 0 complete₃ (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02552 : ⟪ (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02552 = win 3 0 complete₃ (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) (ε) _ _ Eq.refl
wn02553 : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02553 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS) _ _ Eq.refl
wn02554 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02554 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02555 : ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01 ∷ CS01 ∷ CS01⁻ ∷ CS01⁻ ∷ CK10 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02555 = win 3 0 complete₃ ((CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS • (CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS) (ε) _ _ Eq.refl
wn02556 : ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) ⟫ʷ
wn02556 = win 0 3 complete₃ (Toff) (CK₁₀ • CCZ • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02557 : ⟪ (CK21 ∷ CCZ123 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn02557 = win 0 3 complete₃ (CK₁₀ • CCZ • (S ↑ • CK₁₀)) (Toff) _ _ Eq.refl
wn02558 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02558 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S • (S • S • S) • (K • iI) • S • S) (ε) _ _ Eq.refl
wn02559 : ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ
wn02559 = win 0 3 complete₃ (((CS • CS • CS) ↑) • CCZ) (CCZ • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn02560 : ⟪ (Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
wn02560 = win 0 3 complete₃ (Swap • Swap • (Swap ↑) • Swap) (Swap • (Swap ↑) • Swap • (Swap ↑)) _ _ Eq.refl
wn02561 : ⟪ (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CZ01 ∷ []) ⟫ʷ
wn02561 = win 3 0 complete₃ (((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑)) (CX₁₀ • CZ) _ _ Eq.refl
wn02562 : ⟪ [] ⟫ʷ ≈ ⟪ (CZ01 ∷ CZ01 ∷ []) ⟫ʷ
wn02562 = win 3 0 complete₃ (ε) (CZ • CZ) _ _ Eq.refl
wn02563 : ⟪ (CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ []) ⟫ʷ
wn02563 = win 3 0 complete₃ (CZ) (CS • CS) _ _ Eq.refl
wn02564 : ⟪ (CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn02564 = win 3 0 complete₃ (CZ) ((CS • CS • CS) • (CS • CS • CS)) _ _ Eq.refl
wn02565 : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CCZ012 ∷ CS12⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CZ01 ∷ X0 ∷ []) ⟫ʷ
wn02565 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑)) (X • CX₁₀ • CZ • X) _ _ Eq.refl
wn02566 : ⟪ (X2 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wn02566 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (X ↑)) (S) _ _ Eq.refl
wn02567 : ⟪ (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
wn02567 = win 3 0 complete₃ (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ) ((S ↑)) _ _ Eq.refl
wn02568 : ⟪ (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
wn02568 = win 3 0 complete₃ ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ • X • (X ↑)) ((S ↑ ↑)) _ _ Eq.refl
wn02569 : ⟪ (X0 ∷ X2 ∷ CS12 ∷ CCZ012 ∷ X2 ∷ CS01 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wn02569 = win 3 0 complete₃ (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • X • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) (CS) _ _ Eq.refl
wn02570 : ⟪ (CS12 ∷ CCZ012 ∷ X1 ∷ CS02 ∷ CCZ012 ∷ CS02 ∷ CCZ012 ∷ X0 ∷ CS12 ∷ CCZ012 ∷ CS12 ∷ CCZ012 ∷ CCZ012 ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn02570 = win 3 0 complete₃ ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) ((CS ↑)) _ _ Eq.refl
wn02571 : ⟪ (CS23 ∷ CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
wn02571 = win 0 3 complete₃ ((CS ↑) • CCZ • CCZ) ((CS ↑)) _ _ Eq.refl
