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

module Examples.Groups.Clifford+CS.Four.Wins.W48 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn02437 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn02437 = win 0 3 complete₃ (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn02438 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ≈ insʷ 0 (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn02438 = win 0 3 complete₃ (CS • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02439 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • S • (K • iI) • (S • S • S)) ≈ insʷ 3 (S • (K • iI) • (S • S • S) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑))
wn02439 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • (K • iI) • (S • S • S)) (S • (K • iI) • (S • S • S) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02440 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • S • K • (S • S • S)) ≈ insʷ 3 (S • K • (S • S • S) • (X ↑) • CS • (X ↑))
wn02440 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • S • K • (S • S • S)) (S • K • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02441 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (K • iI) • (S • S • S)) ≈ insʷ 3 ((S • S • S) • (K • iI) • (K • iI))
wn02441 = win 3 0 complete₃ ((K • iI) • (K • iI) • (S • S • S)) ((S • S • S) • (K • iI) • (K • iI)) _ _ Eq.refl
wn02442 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K) ≈ insʷ 3 (K • K • S • (K • iI))
wn02442 = win 3 0 complete₃ (S • K) (K • K • S • (K • iI)) _ _ Eq.refl
wn02443 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • (K • iI)) ≈ insʷ 3 ((K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑))
wn02443 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02444 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • K • K • K) ≈ insʷ 3 (K • K • K • (X ↑) • CS • (X ↑))
wn02444 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • K • K • K) (K • K • K • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02445 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) ≈ insʷ 3 ((S • S • S) • (K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑))
wn02445 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) ((S • S • S) • (K • iI) • (K • iI) • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02446 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • K • K • S) ≈ insʷ 3 (K • K • K • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑))
wn02446 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • K • K • S) (K • K • K • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02447 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • (K • iI) • S) ≈ insʷ 3 (S • S • (K • iI) • S)
wn02447 = win 3 0 complete₃ (S • S • (K • iI) • S) (S • S • (K • iI) • S) _ _ Eq.refl
wn02448 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • K • (S • S • S)) ≈ insʷ 3 ((S • S • S) • K • (S • S • S) • (S • S • S) • S)
wn02448 = win 3 0 complete₃ ((S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • S) _ _ Eq.refl
wn02449 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • S • K • S) ≈ insʷ 3 ((S • S • S) • (K • iI) • S • S • (K • iI))
wn02449 = win 3 0 complete₃ ((K • iI) • S • S • K • S) ((S • S • S) • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02450 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ≈ insʷ 3 (K • (S • S • S) • (S • S • S) • K • S • (K • iI))
wn02450 = win 3 0 complete₃ ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • S • (K • iI)) _ _ Eq.refl
wn02451 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • S • (K • iI)) ≈ insʷ 3 ((S • S • S) • (K • iI) • S • S • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑))
wn02451 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • S • (K • iI)) ((S • S • S) • (K • iI) • S • S • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02452 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • S) ≈ insʷ 3 (K • (S • S • S) • (S • S • S) • K • S • (X ↑) • CS • (X ↑))
wn02452 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • S • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02453 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CK₁₀ • (X ↑) • S • S • (K • iI) • S • S • (K • iI)) ≈ insʷ 3 (S • S • (K • iI) • S • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑))
wn02453 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • S • S • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02454 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) ≈ insʷ 3 (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑) • CK₁₀ • (X ↑))
wn02454 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02455 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • S • K • S • S) ≈ insʷ 3 ((S • S • S) • K • S • S)
wn02455 = win 3 0 complete₃ (S • S • S • K • S • S) ((S • S • S) • K • S • S) _ _ Eq.refl
wn02456 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ≈ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • S • S)
wn02456 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • S • S) _ _ Eq.refl
wn02457 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • S • K • (S • S • S) • K • K) ≈ insʷ 3 (S • K • (S • S • S) • K • K • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑))
wn02457 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • K • (S • S • S) • K • K) (S • K • (S • S • S) • K • K • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02458 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ≈ insʷ 3 ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S) • (X ↑) • CS • (X ↑))
wn02458 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02459 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • K • K) ≈ insʷ 3 (K • (S • S • S) • K • K • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑))
wn02459 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • (S • S • S) • K • K) (K • (S • S • S) • K • K • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02460 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • (K • iI) • S • (K • iI)) ≈ insʷ 3 ((K • iI) • (K • iI) • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑))
wn02460 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • S • (K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02461 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • S • S • (K • iI)) ≈ insʷ 3 (S • (K • iI))
wn02461 = win 3 0 complete₃ ((S • S • S) • S • S • (K • iI)) (S • (K • iI)) _ _ Eq.refl
wn02462 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (S • S • S) • (S • S • S)) ≈ insʷ 3 (K • (S • S • S) • (S • S • S))
wn02462 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02463 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • S • S • K • K • K • K) ≈ insʷ 3 (S • (K • iI) • S • (K • iI) • (S • S • S))
wn02463 = win 3 0 complete₃ (K • S • S • K • K • K • K) (S • (K • iI) • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02464 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) ≈ insʷ 3 (S • K • (S • S • S) • K • (S • S • S) • K)
wn02464 = win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) (S • K • (S • S • S) • K • (S • S • S) • K) _ _ Eq.refl
wn02465 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) ≈ insʷ 3 (S • S • (K • iI) • S • (K • iI) • (K • iI))
wn02465 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) (S • S • (K • iI) • S • (K • iI) • (K • iI)) _ _ Eq.refl
wn02466 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • K • (S • S • S) • K • S) ≈ insʷ 3 (K • K • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S))
wn02466 = win 3 0 complete₃ (K • K • (S • S • S) • K • S) (K • K • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02467 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • S • (K • iI) • S • (K • iI) • (K • iI)) ≈ insʷ 3 ((S • S • S) • K • S • S • K)
wn02467 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI) • S • (K • iI) • (K • iI)) ((S • S • S) • K • S • S • K) _ _ Eq.refl
wn02468 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • K • (S • S • S) • K • (S • S • S) • (S • S • S)) ≈ insʷ 3 ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S • (K • iI))
wn02468 = win 3 0 complete₃ (K • K • (S • S • S) • K • (S • S • S) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S • (K • iI)) _ _ Eq.refl
wn02469 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • S • S • K • K • K) ≈ insʷ 3 (S • K • K • K)
wn02469 = win 3 0 complete₃ ((S • S • S) • S • S • K • K • K) (S • K • K • K) _ _ Eq.refl
wn02470 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) ≈ insʷ 3 ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S))
wn02470 = win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02471 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • S • K • K • K) ≈ insʷ 3 ((S • S • S) • K • (S • S • S) • K • K)
wn02471 = win 3 0 complete₃ (K • S • K • K • K) ((S • S • S) • K • (S • S • S) • K • K) _ _ Eq.refl
wn02472 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (K • iI) • (K • iI) • (S • S • S)) ≈ insʷ 3 ((K • iI) • (K • iI) • S • (K • iI) • S • K)
wn02472 = win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • S • K) _ _ Eq.refl
wn02473 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn02473 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02474 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn02474 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02475 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K) ≈ insʷ 3 ((S • S • S) • (K • iI) • (S • S • S) • S • K • S • S • K)
wn02475 = win 3 0 complete₃ (S • K) ((S • S • S) • (K • iI) • (S • S • S) • S • K • S • S • K) _ _ Eq.refl
wn02476 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S • S • S)) ≈ insʷ 3 ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • K • S)
wn02476 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • K • S) _ _ Eq.refl
wn02477 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • S • S • K) ≈ insʷ 3 (X • S • S • S)
wn02477 = win 3 0 complete₃ (S • K • S • S • K) (X • S • S • S) _ _ Eq.refl
wn02478 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • S • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) ≈ insʷ 3 (X)
wn02478 = win 3 0 complete₃ (S • S • S • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (X) _ _ Eq.refl
wn02479 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K) ≈ insʷ 3 ((S • S • S) • K • S • S • S • S • K • S • S • (K • iI))
wn02479 = win 3 0 complete₃ (S • K) ((S • S • S) • K • S • S • S • S • K • S • S • (K • iI)) _ _ Eq.refl
wn02480 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S • S • S)) ≈ insʷ 3 (K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (S • S • S) • (S • S • S) • (K • iI) • S)
wn02480 = win 3 0 complete₃ ((K • iI) • (S • S • S)) (K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (S • S • S) • (S • S • S) • (K • iI) • S) _ _ Eq.refl
wn02481 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • K • S • S • (K • iI)) ≈ insʷ 3 (X • S • S • iI • iI)
wn02481 = win 3 0 complete₃ (S • S • K • S • S • (K • iI)) (X • S • S • iI • iI) _ _ Eq.refl
wn02482 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • iI • iI • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ≈ insʷ 3 (X)
wn02482 = win 3 0 complete₃ (S • S • iI • iI • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (X) _ _ Eq.refl
wn02483 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (K • S • S • K • (K • iI) • S • S • (K • iI))
wn02483 = win 3 0 complete₃ (ε) (K • S • S • K • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02484 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (K • (S • S • S) • (S • S • S) • K • (K • iI) • (S • S • S) • (S • S • S) • (K • iI))
wn02484 = win 3 0 complete₃ (ε) (K • (S • S • S) • (S • S • S) • K • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02485 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • S • (K • iI)) ≈ insʷ 3 (X • iI)
wn02485 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI)) (X • iI) _ _ Eq.refl
wn02486 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (iI • K • (S • S • S) • (S • S • S) • K) ≈ insʷ 3 (X)
wn02486 = win 3 0 complete₃ (iI • K • (S • S • S) • (S • S • S) • K) (X) _ _ Eq.refl
wn02487 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • S) ≈ insʷ 3 (ε)
wn02487 = win 3 0 complete₃ ((S • S • S) • S) (ε) _ _ Eq.refl
wn02488 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (S • S • K • S • S • K • S • S • K • S • S • K)
wn02488 = win 3 0 complete₃ (ε) (S • S • K • S • S • K • S • S • K • S • S • K) _ _ Eq.refl
wn02489 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S))
wn02489 = win 3 0 complete₃ (ε) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02490 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • K • S • S • K) ≈ insʷ 3 (X • S • S • iI)
wn02490 = win 3 0 complete₃ (S • S • K • S • S • K) (X • S • S • iI) _ _ Eq.refl
wn02491 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • S • iI • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ≈ insʷ 3 (X)
wn02491 = win 3 0 complete₃ (S • S • iI • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (X) _ _ Eq.refl
wn02492 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (K • iI) • S • S) ≈ insʷ 3 (S • K • S • S • K • S • S • K)
wn02492 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) (S • K • S • S • K • S • S • K) _ _ Eq.refl
wn02493 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • K • S) ≈ insʷ 3 ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S))
wn02493 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02494 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S • S • S) • S • K) ≈ insʷ 3 (ε)
wn02494 = win 3 0 complete₃ ((K • iI) • (S • S • S) • S • K) (ε) _ _ Eq.refl
wn02495 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • K) ≈ insʷ 3 (S • K • K • S • S • (K • iI))
wn02495 = win 3 0 complete₃ ((S • S • S) • K) (S • K • K • S • S • (K • iI)) _ _ Eq.refl
wn02496 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S) ≈ insʷ 3 (K • (S • S • S) • (S • S • S) • (K • iI) • (K • iI) • (S • S • S))
wn02496 = win 3 0 complete₃ ((K • iI) • S) (K • (S • S • S) • (S • S • S) • (K • iI) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02497 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • S • S • (K • iI)) ≈ insʷ 3 (X)
wn02497 = win 3 0 complete₃ (K • S • S • (K • iI)) (X) _ _ Eq.refl
wn02498 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (S • S • S) • (S • S • S) • (K • iI)) ≈ insʷ 3 (X)
wn02498 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • (K • iI)) (X) _ _ Eq.refl
wn02499 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K) ≈ insʷ 3 ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • CS • CK₁₀)
wn02499 = win 3 0 complete₃ (S • K) ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • CS • CK₁₀) _ _ Eq.refl
wn02500 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S • S • S)) ≈ insʷ 3 ((S ↑ • CK₁₀) • (CS • CS • CS) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑))
wn02500 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((S ↑ • CK₁₀) • (CS • CS • CS) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02501 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • CK₁₀ • (S ↑ • CK₁₀) • (CS • CS • CS)) ≈ insʷ 3 (ε)
wn02501 = win 3 0 complete₃ (CS • CK₁₀ • (S ↑ • CK₁₀) • (CS • CS • CS)) (ε) _ _ Eq.refl
wn02502 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Toff) ≈ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn02502 = win 0 3 complete₃ (Toff) ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn02503 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ≈ insʷ 0 (Toff)
wn02503 = win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • CCZ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (Toff) _ _ Eq.refl
wn02504 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ≈ insʷ 3 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑))
wn02504 = win 3 0 complete₃ ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn02505 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ≈ insʷ 3 ((CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑))
wn02505 = win 3 0 complete₃ ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02506 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑)) ≈ insʷ 3 (ε)
wn02506 = win 3 0 complete₃ ((CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑)) (ε) _ _ Eq.refl
wn02507 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀))
wn02507 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02508 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS)
wn02508 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) _ _ Eq.refl
wn02509 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S • S • S) • (K • iI) • S • S) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn02509 = win 0 3 complete₃ ((S • S • S) • (K • iI) • S • S) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02510 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S • S • S) • (S • S • S) • K • S) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑))
wn02510 = win 0 3 complete₃ ((S • S • S) • (S • S • S) • K • S) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02511 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 (ε)
wn02511 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn02512 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • S • (K • iI) • (S • S • S)) ≈ insʷ 3 ((K • iI) • (S • S • S))
wn02512 = win 3 0 complete₃ ((S • S • S) • S • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02513 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • (S • S • S)) ≈ insʷ 3 (S • K • (S • S • S))
wn02513 = win 3 0 complete₃ (S • K • (S • S • S)) (S • K • (S • S • S)) _ _ Eq.refl
wn02514 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (K • iI) • (K • iI) • (K • iI)) ≈ insʷ 3 ((S • S • S) • (K • iI) • (K • iI) • (K • iI))
wn02514 = win 3 0 complete₃ ((S • S • S) • (K • iI) • (K • iI) • (K • iI)) ((S • S • S) • (K • iI) • (K • iI) • (K • iI)) _ _ Eq.refl
wn02515 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • K • K) ≈ insʷ 3 (K • K • K • S • (S • S • S))
wn02515 = win 3 0 complete₃ (K • K • K) (K • K • K • S • (S • S • S)) _ _ Eq.refl
wn02516 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) ≈ insʷ 3 (S • (K • iI) • S)
wn02516 = win 3 0 complete₃ (K • (S • S • S) • (K • iI) • (K • iI) • (K • iI)) (S • (K • iI) • S) _ _ Eq.refl
wn02517 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • K • K • S) ≈ insʷ 3 ((S • S • S) • K • (S • S • S) • K)
wn02517 = win 3 0 complete₃ (K • K • K • S) ((S • S • S) • K • (S • S • S) • K) _ _ Eq.refl
wn02518 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • S • S • (K • iI)) ≈ insʷ 3 (S • S • (K • iI) • S • S • (K • iI))
wn02518 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • S • (K • iI)) (S • S • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02519 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (S • S • S) • (S • S • S) • K • S) ≈ insʷ 3 (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S))
wn02519 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02520 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • S • (K • iI) • S • S • (K • iI)) ≈ insʷ 3 (S • S • K • S • S)
wn02520 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI) • S • S • (K • iI)) (S • S • K • S • S) _ _ Eq.refl
wn02521 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) ≈ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI))
wn02521 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02522 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • S • K • (S • S • S) • K • K) ≈ insʷ 3 (K • (S • S • S) • K • K)
wn02522 = win 3 0 complete₃ ((S • S • S) • S • K • (S • S • S) • K • K) (K • (S • S • S) • K • K) _ _ Eq.refl
wn02523 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ≈ insʷ 3 ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S))
wn02523 = win 3 0 complete₃ ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02524 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • K • (S • S • S) • K • K) ≈ insʷ 3 ((S • S • S) • K • K • K • K)
wn02524 = win 3 0 complete₃ (K • K • (S • S • S) • K • K) ((S • S • S) • K • K • K • K) _ _ Eq.refl
wn02525 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (K • iI) • S • (K • iI)) ≈ insʷ 3 ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • K)
wn02525 = win 3 0 complete₃ ((K • iI) • (K • iI) • S • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • K) _ _ Eq.refl
wn02526 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • (K • iI) • S • S • (K • iI) • S) ≈ insʷ 3 (S • (K • iI) • S • S • (K • iI) • S)
wn02526 = win 3 0 complete₃ (S • (K • iI) • S • S • (K • iI) • S) (S • (K • iI) • S • S • (K • iI) • S) _ _ Eq.refl
wn02527 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) ≈ insʷ 3 ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S))
wn02527 = win 3 0 complete₃ ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) _ _ Eq.refl
wn02528 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • (K • iI) • S • S • (K • iI) • S) ≈ insʷ 3 (X • iI • iI)
wn02528 = win 3 0 complete₃ (S • (K • iI) • S • S • (K • iI) • S) (X • iI • iI) _ _ Eq.refl
wn02529 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (iI • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) ≈ insʷ 3 (X)
wn02529 = win 3 0 complete₃ (iI • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K • (S • S • S)) (X) _ _ Eq.refl
wn02530 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (K • iI) • S • S) ≈ insʷ 3 (S • (K • iI) • (S • S • S) • (K • iI) • S • S • (K • iI) • S)
wn02530 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) (S • (K • iI) • (S • S • S) • (K • iI) • S • S • (K • iI) • S) _ _ Eq.refl
wn02531 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • K • S) ≈ insʷ 3 ((S • S • S) • K • (S • S • S) • (S • S • S) • K • S • K • (S • S • S))
wn02531 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((S • S • S) • K • (S • S • S) • (S • S • S) • K • S • K • (S • S • S)) _ _ Eq.refl
wn02532 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • S • (K • iI) • S) ≈ insʷ 3 (X • S • iI)
wn02532 = win 3 0 complete₃ ((K • iI) • S • S • (K • iI) • S) (X • S • iI) _ _ Eq.refl
wn02533 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K) ≈ insʷ 3 (X)
wn02533 = win 3 0 complete₃ (S • iI • (S • S • S) • K • (S • S • S) • (S • S • S) • K) (X) _ _ Eq.refl
wn02534 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (X • (X ↑) • X • (X ↑)) ≈ insʷ 3 (ε)
wn02534 = win 3 0 complete₃ (X • (X ↑) • X • (X ↑)) (ε) _ _ Eq.refl
wn02535 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (X ↑ ↑))
wn02535 = win 3 0 complete₃ ((X ↑) • (Swap ↑)) ((Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02536 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) ≈ insʷ 3 (S • S • (K • iI) • (S • S • S))
wn02536 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02537 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • S • S) ≈ insʷ 3 (S • K • (S • S • S) • (S • S • S))
wn02537 = win 3 0 complete₃ (S • K • S • S) (S • K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02538 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • S • K • S • S • K) ≈ insʷ 3 ((K • iI) • (S • S • S))
wn02538 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S • K • S • S • K) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02539 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S • S • S) • (S • S • S) • (K • iI)) ≈ insʷ 3 (S • K • (S • S • S) • (S • S • S) • (K • iI) • S)
wn02539 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S) • (K • iI)) (S • K • (S • S • S) • (S • S • S) • (K • iI) • S) _ _ Eq.refl
wn02540 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) ≈ insʷ 3 (S • S • (K • iI) • S • S)
wn02540 = win 3 0 complete₃ ((S • S • S) • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) (S • S • (K • iI) • S • S) _ _ Eq.refl
wn02541 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • S) ≈ insʷ 3 ((S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S))
wn02541 = win 3 0 complete₃ (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • S) ((S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn02542 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • CCZ • ((CS • CS • CS) ↑) • (K • iI) • (S • S • S)) ≈ insʷ 3 (((CS • CS • CS) ↑) • S • Toff • (S • S • S))
wn02542 = win 3 0 complete₃ (S • K • CCZ • ((CS • CS • CS) ↑) • (K • iI) • (S • S • S)) (((CS • CS • CS) ↑) • S • Toff • (S • S • S)) _ _ Eq.refl
wn02543 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • S • (S • S • S)) ≈ insʷ 3 (S • K)
wn02543 = win 3 0 complete₃ (S • K • S • (S • S • S)) (S • K) _ _ Eq.refl
wn02544 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • S • K • S • S • K) ≈ insʷ 3 ((K • iI) • (S • S • S))
wn02544 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • S • S • K • S • S • K) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02545 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ≈ insʷ 3 (S • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S))
wn02545 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) (S • K • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02546 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) ≈ insʷ 3 ((K • iI) • S • S)
wn02546 = win 3 0 complete₃ (S • K • S • S • (S • S • S) • (K • iI) • (S • S • S)) ((K • iI) • S • S) _ _ Eq.refl
wn02547 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) ≈ insʷ 3 ((S • S • S) • (S • S • S) • K)
wn02547 = win 3 0 complete₃ (S • K • S • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) ((S • S • S) • (S • S • S) • K) _ _ Eq.refl
wn02548 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑) • S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑)) ≈ insʷ 3 (CZ • CX₁₀)
wn02548 = win 3 0 complete₃ (S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑) • S • K • (CS ↑) • CCZ • (K • iI) • (S • S • S) • (X ↑ ↑)) (CZ • CX₁₀) _ _ Eq.refl
wn02549 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((S • S • S) ↑) • Swap) ≈ insʷ 3 (Swap • (S • S • S))
wn02549 = win 3 0 complete₃ (((S • S • S) ↑) • Swap) (Swap • (S • S • S)) _ _ Eq.refl
wn02550 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) ≈ insʷ 3 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑))
wn02550 = win 3 0 complete₃ (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn02551 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑))
wn02551 = win 3 0 complete₃ (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02552 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) ≈ insʷ 3 (ε)
wn02552 = win 3 0 complete₃ (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) (ε) _ _ Eq.refl
wn02553 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (K • iI) • S • S) ≈ insʷ 3 ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS)
wn02553 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS) _ _ Eq.refl
wn02554 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • K • S) ≈ insʷ 3 ((CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑))
wn02554 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02555 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS • (CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS) ≈ insʷ 3 (ε)
wn02555 = win 3 0 complete₃ ((CS • CS • CS) • (S ↑ • CK₁₀) • CS • CS • (CS • CS • CS) • (CS • CS • CS) • CK₁₀ • CS) (ε) _ _ Eq.refl
wn02556 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Toff) ≈ insʷ 0 (CK₁₀ • CCZ • (S ↑ • CK₁₀))
wn02556 = win 0 3 complete₃ (Toff) (CK₁₀ • CCZ • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02557 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CK₁₀ • CCZ • (S ↑ • CK₁₀)) ≈ insʷ 0 (Toff)
wn02557 = win 0 3 complete₃ (CK₁₀ • CCZ • (S ↑ • CK₁₀)) (Toff) _ _ Eq.refl
wn02558 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (S • S • S) • K • S • (S • S • S) • (K • iI) • S • S) ≈ insʷ 3 (ε)
wn02558 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S • (S • S • S) • (K • iI) • S • S) (ε) _ _ Eq.refl
wn02559 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((CS • CS • CS) ↑) • CCZ) ≈ insʷ 0 (CCZ • ((CS • CS • CS) ↑))
wn02559 = win 0 3 complete₃ (((CS • CS • CS) ↑) • CCZ) (CCZ • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn02560 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • Swap • (Swap ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑) • Swap • (Swap ↑))
wn02560 = win 0 3 complete₃ (Swap • Swap • (Swap ↑) • Swap) (Swap • (Swap ↑) • Swap • (Swap ↑)) _ _ Eq.refl
wn02561 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑)) ≈ insʷ 3 (CX₁₀ • CZ)
wn02561 = win 3 0 complete₃ (((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑)) (CX₁₀ • CZ) _ _ Eq.refl
wn02562 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (CZ • CZ)
wn02562 = win 3 0 complete₃ (ε) (CZ • CZ) _ _ Eq.refl
wn02563 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CZ) ≈ insʷ 3 (CS • CS)
wn02563 = win 3 0 complete₃ (CZ) (CS • CS) _ _ Eq.refl
wn02564 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CZ) ≈ insʷ 3 ((CS • CS • CS) • (CS • CS • CS))
wn02564 = win 3 0 complete₃ (CZ) ((CS • CS • CS) • (CS • CS • CS)) _ _ Eq.refl
wn02565 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑)) ≈ insʷ 3 (X • CX₁₀ • CZ • X)
wn02565 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S • CCZ • ((CS • CS • CS) ↑) • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑)) (X • CX₁₀ • CZ • X) _ _ Eq.refl
wn02566 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (X ↑)) ≈ insʷ 3 (S)
wn02566 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • (X ↑)) (S) _ _ Eq.refl
wn02567 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ) ≈ insʷ 3 ((S ↑))
wn02567 = win 3 0 complete₃ (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • CS • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ) ((S ↑)) _ _ Eq.refl
wn02568 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ • X • (X ↑)) ≈ insʷ 3 ((S ↑ ↑))
wn02568 = win 3 0 complete₃ ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • (CS ↑) • CCZ • X • (X ↑)) ((S ↑ ↑)) _ _ Eq.refl
wn02569 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • X • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) ≈ insʷ 3 (CS)
wn02569 = win 3 0 complete₃ (X • (X ↑ ↑) • (CS ↑) • CCZ • (X ↑ ↑) • CS • CCZ • X • (CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) (CS) _ _ Eq.refl
wn02570 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) ≈ insʷ 3 ((CS ↑))
wn02570 = win 3 0 complete₃ ((CS ↑) • CCZ • (X ↑) • (Swap ↑ • CS • Swap ↑) • CCZ • (Swap ↑ • CS • Swap ↑) • CCZ • X • (CS ↑) • CCZ • (CS ↑) • CCZ • CCZ • X • (X ↑)) ((CS ↑)) _ _ Eq.refl
wn02571 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • CCZ • CCZ) ≈ insʷ 0 ((CS ↑))
wn02571 = win 0 3 complete₃ ((CS ↑) • CCZ • CCZ) ((CS ↑)) _ _ Eq.refl
