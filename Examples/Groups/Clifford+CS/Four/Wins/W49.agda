------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the four-wire derivations, each decided once
--
-- Each lemma is one window step of Four/D: two words on three wires with
-- the same operator, equal by completeness on three wires
-- (Windows.win, one evaluation).  Written by scratchpad/four/winlib4.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Wins.W49 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn02572 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • X • (X ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • X • (X ↑)) ≈ insʷ 3 (X)
wn02572 = win 3 0 complete₃ (S • S • X • (X ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • X • (X ↑)) (X) _ _ Eq.refl
wn02573 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((S • S • S) ↑ ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • ((S • S • S) ↑))
wn02573 = win 3 0 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn02574 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((K • iI) ↑ ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • ((K • iI) ↑))
wn02574 = win 3 0 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn02575 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑) • (S ↑) • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑)) ≈ insʷ 3 ((X ↑))
wn02575 = win 3 0 complete₃ ((S ↑) • (S ↑) • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑)) ((X ↑)) _ _ Eq.refl
wn02576 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑))
wn02576 = win 3 0 complete₃ ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑)) _ _ Eq.refl
wn02577 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑) • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑))
wn02577 = win 3 0 complete₃ ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑) • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑)) _ _ Eq.refl
wn02578 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((S ↑) • ((S • S • S) ↑))
wn02578 = win 3 0 complete₃ (ε) ((S ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn02579 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((K ↑) • ((K • iI) ↑))
wn02579 = win 3 0 complete₃ (ε) ((K ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn02580 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (((S • S • S) ↑) • (S ↑))
wn02580 = win 3 0 complete₃ (ε) (((S • S • S) ↑) • (S ↑)) _ _ Eq.refl
wn02581 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((S • S • S) ↑) • (S ↑)) ≈ insʷ 3 (ε)
wn02581 = win 3 0 complete₃ (((S • S • S) ↑) • (S ↑)) (ε) _ _ Eq.refl
wn02582 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑) • ((K • iI) ↑)) ≈ insʷ 3 (ε)
wn02582 = win 3 0 complete₃ ((K ↑) • ((K • iI) ↑)) (ε) _ _ Eq.refl
wn02583 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑) • ((S • S • S) ↑)) ≈ insʷ 3 (ε)
wn02583 = win 3 0 complete₃ ((S ↑) • ((S • S • S) ↑)) (ε) _ _ Eq.refl
wn02584 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CX₁₀ • CZ • CZ • CX₀₁ • CX₁₀ • CZ) ≈ insʷ 3 (CZ • Swap)
wn02584 = win 3 0 complete₃ (CX₁₀ • CZ • CZ • CX₀₁ • CX₁₀ • CZ) (CZ • Swap) _ _ Eq.refl
