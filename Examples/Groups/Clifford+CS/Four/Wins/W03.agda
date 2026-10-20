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

module Examples.Groups.Clifford+CS.Four.Wins.W03 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn00409 : (₁₊ (1 +ℕ 2)) ⊢ insʷ 1 ((CS ↑) • (S • S • S)) ≈ insʷ 1 ((S • S • S) • (CS ↑))
wn00409 = win 1 2 complete₃ ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00410 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (CS ↑)) ≈ insʷ 0 ((CS ↑) • (Swap ↑ • CS • Swap ↑))
wn00410 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00411 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ≈ insʷ 0 ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑))
wn00411 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00412 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • CS) ≈ insʷ 0 (CS • (CS ↑))
wn00412 = win 0 3 complete₃ ((CS ↑) • CS) (CS • (CS ↑)) _ _ Eq.refl
wn00413 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑))
wn00413 = win 0 3 complete₃ ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00414 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CX₀₁ ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (CX₁₀ ↑))
wn00414 = win 3 0 complete₃ ((CX₀₁ ↑) • (Swap ↑)) ((Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00415 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CZ) ≈ insʷ 3 (CZ • (Swap ↑ • CS • Swap ↑))
wn00415 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CZ) (CZ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00416 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • CS)
wn00416 = win 0 3 complete₃ (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) _ _ Eq.refl
wn00417 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) ≈ insʷ 3 (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00417 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00418 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS • CS • CS) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • (CS • CS • CS))
wn00418 = win 0 3 complete₃ ((CS • CS • CS) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00419 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) ≈ insʷ 0 (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑))
wn00419 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00420 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (iI ↑ ↑)) ≈ insʷ 0 ((iI ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00420 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00421 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑ ↑)) ≈ insʷ 0 (((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00421 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00422 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (S ↑ ↑)) ≈ insʷ 0 ((S ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00422 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (S ↑ ↑)) ((S ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00423 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑))
wn00423 = win 3 0 complete₃ ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00424 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ≈ insʷ 3 ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑))
wn00424 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00425 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • (CS ↑))
wn00425 = win 3 0 complete₃ ((CS ↑) • (CS • CS • CS)) ((CS • CS • CS) • (CS ↑)) _ _ Eq.refl
wn00426 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (iI ↑ ↑)) ≈ insʷ 0 ((iI ↑ ↑) • (CS ↑))
wn00426 = win 0 3 complete₃ ((CS ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00427 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • ((S • S • S) ↑ ↑)) ≈ insʷ 0 (((S • S • S) ↑ ↑) • (CS ↑))
wn00427 = win 0 3 complete₃ ((CS ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00428 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (S ↑ ↑)) ≈ insʷ 0 ((S ↑ ↑) • (CS ↑))
wn00428 = win 0 3 complete₃ ((CS ↑) • (S ↑ ↑)) ((S ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00429 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toffᵗ • iI) ≈ insʷ 3 (iI • Toffᵗ)
wn00429 = win 3 0 complete₃ (Toffᵗ • iI) (iI • Toffᵗ) _ _ Eq.refl
wn00430 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((CS • CS • CS) ↑) • (iI ↑ ↑)) ≈ insʷ 0 ((iI ↑ ↑) • ((CS • CS • CS) ↑))
wn00430 = win 0 3 complete₃ (((CS • CS • CS) ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00431 : (₁₊ (1 +ℕ 2)) ⊢ insʷ 1 ((S • S • S) • ((CS • CS • CS) ↑)) ≈ insʷ 1 (((CS • CS • CS) ↑) • (S • S • S))
wn00431 = win 1 2 complete₃ ((S • S • S) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S • S • S)) _ _ Eq.refl
wn00432 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((S • S • S) ↑ ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • ((S • S • S) ↑ ↑))
wn00432 = win 0 3 complete₃ (((S • S • S) ↑ ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn00433 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑))
wn00433 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00434 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • Swap) ≈ insʷ 3 (Swap • ((S • S • S) ↑))
wn00434 = win 3 0 complete₃ ((S • S • S) • Swap) (Swap • ((S • S • S) ↑)) _ _ Eq.refl
wn00435 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (iI • Swap) ≈ insʷ 3 (Swap • iI)
wn00435 = win 3 0 complete₃ (iI • Swap) (Swap • iI) _ _ Eq.refl
wn00436 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (CS ↑))
wn00436 = win 0 3 complete₃ ((CS ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00437 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • iI) ≈ insʷ 3 (iI • Swap)
wn00437 = win 3 0 complete₃ (Swap • iI) (iI • Swap) _ _ Eq.refl
wn00438 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toffᵗ • (S • S • S)) ≈ insʷ 3 ((S • S • S) • Toffᵗ)
wn00438 = win 3 0 complete₃ (Toffᵗ • (S • S • S)) ((S • S • S) • Toffᵗ) _ _ Eq.refl
wn00439 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((CS • CS • CS) ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑))
wn00439 = win 0 3 complete₃ (((CS • CS • CS) ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00440 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (S ↑)) ≈ insʷ 0 ((S ↑) • (CS ↑))
wn00440 = win 0 3 complete₃ ((CS ↑) • (S ↑)) ((S ↑) • (CS ↑)) _ _ Eq.refl
wn00441 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • ((S • S • S) ↑)) ≈ insʷ 0 (((S • S • S) ↑) • (CS ↑))
wn00441 = win 0 3 complete₃ ((CS ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (CS ↑)) _ _ Eq.refl
wn00442 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • S) ≈ insʷ 0 (S • (CS ↑))
wn00442 = win 0 3 complete₃ ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
wn00443 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (S • S • S)) ≈ insʷ 0 ((S • S • S) • (CS ↑))
wn00443 = win 0 3 complete₃ ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00444 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • CS) ≈ insʷ 3 (CS • CCZ)
wn00444 = win 3 0 complete₃ (CCZ • CS) (CS • CCZ) _ _ Eq.refl
wn00445 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • (S ↑))
wn00445 = win 0 3 complete₃ ((S ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S ↑)) _ _ Eq.refl
wn00446 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • CCZ)
wn00446 = win 3 0 complete₃ (CCZ • (CS • CS • CS)) ((CS • CS • CS) • CCZ) _ _ Eq.refl
wn00447 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((S • S • S) ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • ((S • S • S) ↑))
wn00447 = win 0 3 complete₃ (((S • S • S) ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00448 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 0 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn00448 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00449 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 0 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑))
wn00449 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00450 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 0 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑))
wn00450 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00451 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 0 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑))
wn00451 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00452 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (S ↑) • (K ↑)) ≈ insʷ 3 (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑))
wn00452 = win 3 0 complete₃ ((X ↑) • (S ↑) • (K ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) _ _ Eq.refl
wn00453 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑)) ≈ insʷ 3 (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑))
wn00453 = win 3 0 complete₃ (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) _ _ Eq.refl
wn00454 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (CS • CS • CS) • (X ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑) • (CS • CS • CS) • (X ↑))
wn00454 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • Toff) (Toff • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00455 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑))
wn00455 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00456 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑))
wn00456 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00457 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CX₁₀ • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • CX₁₀)
wn00457 = win 0 3 complete₃ (CX₁₀ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CX₁₀) _ _ Eq.refl
wn00458 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ≈ insʷ 3 (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff)
wn00458 = win 3 0 complete₃ ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff) _ _ Eq.refl
wn00459 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • X) ≈ insʷ 3 (X • (S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00459 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • X) (X • (S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00460 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀) ≈ insʷ 3 (CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ)
wn00460 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀) (CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00461 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (CZ ↑) • CCZ)
wn00461 = win 3 0 complete₃ (CCZ • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CZ ↑) • CCZ) _ _ Eq.refl
wn00462 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑))
wn00462 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00463 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00463 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00464 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑ ↑) • (Swap ↑)) ≈ insʷ 0 ((Swap ↑) • (S ↑))
wn00464 = win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) _ _ Eq.refl
wn00465 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑))
wn00465 = win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00466 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • Toff) ≈ insʷ 3 (Toff • (CZ ↑) • CCZ)
wn00466 = win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) _ _ Eq.refl
wn00467 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CZ ↑) • Toff) ≈ insʷ 3 (Toff • (CZ ↑))
wn00467 = win 3 0 complete₃ ((CZ ↑) • Toff) (Toff • (CZ ↑)) _ _ Eq.refl
wn00468 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • Toff) ≈ insʷ 3 (Toff • ((CS • CS • CS) ↑))
wn00468 = win 3 0 complete₃ (((CS • CS • CS) ↑) • Toff) (Toff • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00469 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • Toff) ≈ insʷ 3 (Toff • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ)
wn00469 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Toff) (Toff • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) _ _ Eq.refl
wn00470 : (₁₊ (1 +ℕ 2)) ⊢ insʷ 1 (S • ((CS • CS • CS) ↑)) ≈ insʷ 1 (((CS • CS • CS) ↑) • S)
wn00470 = win 1 2 complete₃ (S • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • S) _ _ Eq.refl
wn00471 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00471 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00472 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • iI) ≈ insʷ 3 (iI • (K ↑ • CCZ • K ↑ • iI))
wn00472 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • iI) (iI • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00473 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (iI ↑ ↑)) ≈ insʷ 0 ((iI ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00473 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00474 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑ ↑)) ≈ insʷ 0 (((S • S • S) ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00474 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00475 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ ↑)) ≈ insʷ 0 ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00475 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ ↑)) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00476 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑) • (Swap ↑)) ≈ insʷ 0 ((Swap ↑) • (S ↑ ↑))
wn00476 = win 0 3 complete₃ ((S ↑) • (Swap ↑)) ((Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00477 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑ ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (S ↑))
wn00477 = win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) _ _ Eq.refl
wn00478 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CX₁₀ ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (CX₀₁ ↑))
wn00478 = win 3 0 complete₃ ((CX₁₀ ↑) • (Swap ↑)) ((Swap ↑) • (CX₀₁ ↑)) _ _ Eq.refl
wn00479 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (S ↑ ↑))
wn00479 = win 3 0 complete₃ ((S ↑) • (Swap ↑)) ((Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00480 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CK₀₁ • Swap) ≈ insʷ 3 (Swap • CK₁₀)
wn00480 = win 3 0 complete₃ (CK₀₁ • Swap) (Swap • CK₁₀) _ _ Eq.refl
wn00481 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • Swap) ≈ insʷ 3 (Swap • (S ↑))
wn00481 = win 3 0 complete₃ (S • Swap) (Swap • (S ↑)) _ _ Eq.refl
wn00482 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑))
wn00482 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00483 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00483 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00484 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00484 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00485 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn00485 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00486 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑))
wn00486 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00487 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑))
wn00487 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00488 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00488 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00489 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00489 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00490 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn00490 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00491 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀)
wn00491 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00492 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀)
wn00492 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00493 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀)
wn00493 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00494 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑))
wn00494 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00495 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑))
wn00495 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00496 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00496 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00497 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00497 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00498 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀)
wn00498 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00499 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀)
wn00499 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00500 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑))
wn00500 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00501 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (S ↑))
wn00501 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00502 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00502 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00503 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00503 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00504 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀)
wn00504 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00505 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) ≈ insʷ 3 (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00505 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00506 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) ≈ insʷ 3 (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn00506 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00507 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ≈ insʷ 3 (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00507 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
