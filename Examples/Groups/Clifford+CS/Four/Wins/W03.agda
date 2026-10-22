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

module Examples.Groups.Clifford+CS.Four.Wins.W03 where

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

wn00409 : Base 3 → ⟪ (CS23 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00409 b = win 1 2 b ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00410 : Base 3 → ⟪ (CS13 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS13 ∷ []) ⟫ʷ
wn00410 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00411 : Base 3 → ⟪ (CX31 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX31 ∷ []) ⟫ʷ
wn00411 b = win 0 3 b ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00412 : Base 3 → ⟪ (CS23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS23 ∷ []) ⟫ʷ
wn00412 b = win 0 3 b ((CS ↑) • CS) (CS • (CS ↑)) _ _ Eq.refl
wn00413 : Base 3 → ⟪ (CS23 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
wn00413 b = win 0 3 b ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00414 : Base 3 → ⟪ (CX12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX21 ∷ []) ⟫ʷ
wn00414 b = win 3 0 b ((CX₀₁ ↑) • (Swap ↑)) ((Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00415 : Base 3 → ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ
wn00415 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • CZ) (CZ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00416 : Base 3 → ⟪ (CS12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00416 b = win 0 3 b (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) _ _ Eq.refl
wn00417 : Base 3 → ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00417 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00418 : Base 3 → ⟪ (CS12⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00418 b = win 0 3 b ((CS • CS • CS) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00419 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn00419 b = win 0 3 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00420 : Base 3 → ⟪ (CS13 ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS13 ∷ []) ⟫ʷ
wn00420 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00421 : Base 3 → ⟪ (CS13 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00421 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00422 : Base 3 → ⟪ (CS13 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13 ∷ []) ⟫ʷ
wn00422 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (S ↑ ↑)) ((S ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00423 : Base 3 → ⟪ (CS12 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn00423 b = win 3 0 b ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00424 : Base 3 → ⟪ (CX20 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX20 ∷ []) ⟫ʷ
wn00424 b = win 3 0 b ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00425 : Base 3 → ⟪ (CS12 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00425 b = win 3 0 b ((CS ↑) • (CS • CS • CS)) ((CS • CS • CS) • (CS ↑)) _ _ Eq.refl
wn00426 : Base 3 → ⟪ (CS23 ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS23 ∷ []) ⟫ʷ
wn00426 b = win 0 3 b ((CS ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00427 : Base 3 → ⟪ (CS23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00427 b = win 0 3 b ((CS ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00428 : Base 3 → ⟪ (CS23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS23 ∷ []) ⟫ʷ
wn00428 b = win 0 3 b ((CS ↑) • (S ↑ ↑)) ((S ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00429 : Base 3 → ⟪ (Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff201 ∷ []) ⟫ʷ
wn00429 b = win 3 0 b (Toffᵗ • iI) (iI • Toffᵗ) _ _ Eq.refl
wn00430 : Base 3 → ⟪ (CS23⁻ ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00430 b = win 0 3 b (((CS • CS • CS) ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00431 : Base 3 → ⟪ (S0⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn00431 b = win 1 2 b ((S • S • S) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S • S • S)) _ _ Eq.refl
wn00432 : Base 3 → ⟪ (S3⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S3⁻ ∷ []) ⟫ʷ
wn00432 b = win 0 3 b (((S • S • S) ↑ ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn00433 : Base 3 → ⟪ (CS13 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00433 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00434 : Base 3 → ⟪ (S0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1⁻ ∷ []) ⟫ʷ
wn00434 b = win 3 0 b ((S • S • S) • Swap) (Swap • ((S • S • S) ↑)) _ _ Eq.refl
wn00435 : Base 3 → ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ
wn00435 b = win 3 0 b (iI • Swap) (Swap • iI) _ _ Eq.refl
wn00436 : Base 3 → ⟪ (CS23 ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23 ∷ []) ⟫ʷ
wn00436 b = win 0 3 b ((CS ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00437 : Base 3 → ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ
wn00437 b = win 3 0 b (Swap • iI) (iI • Swap) _ _ Eq.refl
wn00438 : Base 3 → ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ
wn00438 b = win 3 0 b (Toffᵗ • (S • S • S)) ((S • S • S) • Toffᵗ) _ _ Eq.refl
wn00439 : Base 3 → ⟪ (CS23⁻ ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00439 b = win 0 3 b (((CS • CS • CS) ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00440 : Base 3 → ⟪ (CS23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS23 ∷ []) ⟫ʷ
wn00440 b = win 0 3 b ((CS ↑) • (S ↑)) ((S ↑) • (CS ↑)) _ _ Eq.refl
wn00441 : Base 3 → ⟪ (CS23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00441 b = win 0 3 b ((CS ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (CS ↑)) _ _ Eq.refl
wn00442 : Base 3 → ⟪ (CS23 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS23 ∷ []) ⟫ʷ
wn00442 b = win 0 3 b ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
wn00443 : Base 3 → ⟪ (CS23 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00443 b = win 0 3 b ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00444 : Base 3 → ⟪ (CCZ012 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ012 ∷ []) ⟫ʷ
wn00444 b = win 3 0 b (CCZ • CS) (CS • CCZ) _ _ Eq.refl
wn00445 : Base 3 → ⟪ (S2 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2 ∷ []) ⟫ʷ
wn00445 b = win 0 3 b ((S ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S ↑)) _ _ Eq.refl
wn00446 : Base 3 → ⟪ (CCZ012 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00446 b = win 3 0 b (CCZ • (CS • CS • CS)) ((CS • CS • CS) • CCZ) _ _ Eq.refl
wn00447 : Base 3 → ⟪ (S2⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2⁻ ∷ []) ⟫ʷ
wn00447 b = win 0 3 b (((S • S • S) ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00448 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn00448 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00449 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00449 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00450 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00450 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00451 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn00451 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00452 : Base 3 → ⟪ (X1 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ
wn00452 b = win 3 0 b ((X ↑) • (S ↑) • (K ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) _ _ Eq.refl
wn00453 : Base 3 → ⟪ (K1⁻ ∷ S1⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ
wn00453 b = win 3 0 b (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) _ _ Eq.refl
wn00454 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00454 b = win 3 0 b ((X ↑) • (CS • CS • CS) • (X ↑) • Toff) (Toff • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00455 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00455 b = win 3 0 b ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00456 : Base 3 → ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00456 b = win 3 0 b ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00457 : Base 3 → ⟪ (CX21 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CX21 ∷ []) ⟫ʷ
wn00457 b = win 0 3 b (CX₁₀ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CX₁₀) _ _ Eq.refl
wn00458 : Base 3 → ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) ⟫ʷ
wn00458 b = win 3 0 b ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff) _ _ Eq.refl
wn00459 : Base 3 → ⟪ (CS02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00459 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • X) (X • (S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00460 : Base 3 → ⟪ (CS02⁻ ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00460 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀) (CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00461 : Base 3 → ⟪ (CCZ012 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00461 b = win 3 0 b (CCZ • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CZ ↑) • CCZ) _ _ Eq.refl
wn00462 : Base 3 → ⟪ (CS12⁻ ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00462 b = win 3 0 b (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00463 : Base 3 → ⟪ (CS02⁻ ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00463 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00464 : Base 3 → ⟪ (S3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S2 ∷ []) ⟫ʷ
wn00464 b = win 0 3 b ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) _ _ Eq.refl
wn00465 : Base 3 → ⟪ (S2 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ S2 ∷ []) ⟫ʷ
wn00465 b = win 3 0 b ((S ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00466 : Base 3 → ⟪ (CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00466 b = win 3 0 b (CCZ • Toff) (Toff • (CZ ↑) • CCZ) _ _ Eq.refl
wn00467 : Base 3 → ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ
wn00467 b = win 3 0 b ((CZ ↑) • Toff) (Toff • (CZ ↑)) _ _ Eq.refl
wn00468 : Base 3 → ⟪ (CS12⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00468 b = win 3 0 b (((CS • CS • CS) ↑) • Toff) (Toff • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00469 : Base 3 → ⟪ (CS02 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00469 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • Toff) (Toff • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) _ _ Eq.refl
wn00470 : Base 3 → ⟪ (S0 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0 ∷ []) ⟫ʷ
wn00470 b = win 1 2 b (S • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • S) _ _ Eq.refl
wn00471 : Base 3 → ⟪ (CS13⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn00471 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00472 : Base 3 → ⟪ (Toff102 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff102 ∷ []) ⟫ʷ
wn00472 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • iI) (iI • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00473 : Base 3 → ⟪ (CS13⁻ ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00473 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00474 : Base 3 → ⟪ (CS13⁻ ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn00474 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00475 : Base 3 → ⟪ (CS13⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00475 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ ↑)) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00476 : Base 3 → ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ
wn00476 b = win 0 3 b ((S ↑) • (Swap ↑)) ((Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00477 : Base 3 → ⟪ (S2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1 ∷ []) ⟫ʷ
wn00477 b = win 3 0 b ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) _ _ Eq.refl
wn00478 : Base 3 → ⟪ (CX21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX12 ∷ []) ⟫ʷ
wn00478 b = win 3 0 b ((CX₁₀ ↑) • (Swap ↑)) ((Swap ↑) • (CX₀₁ ↑)) _ _ Eq.refl
wn00479 : Base 3 → ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ
wn00479 b = win 3 0 b ((S ↑) • (Swap ↑)) ((Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00480 : Base 3 → ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ
wn00480 b = win 3 0 b (CK₀₁ • Swap) (Swap • CK₁₀) _ _ Eq.refl
wn00481 : Base 3 → ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ
wn00481 b = win 3 0 b (S • Swap) (Swap • (S ↑)) _ _ Eq.refl
wn00482 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00482 b = win 0 3 b ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00483 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00483 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00484 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00484 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00485 : Base 3 → ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00485 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00486 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CX31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CX31 ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00486 b = win 0 3 b ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00487 : Base 3 → ⟪ (S2 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ S2 ∷ []) ⟫ʷ
wn00487 b = win 0 3 b ((S ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00488 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00488 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00489 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00489 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00490 : Base 3 → ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00490 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00491 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00491 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00492 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00492 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00493 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00493 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00494 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00494 b = win 0 3 b ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00495 : Base 3 → ⟪ (S2 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ S2 ∷ []) ⟫ʷ
wn00495 b = win 0 3 b ((S ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00496 : Base 3 → ⟪ (CK20 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
wn00496 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00497 : Base 3 → ⟪ (CS02 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00497 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00498 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00498 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00499 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00499 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00500 : Base 3 → ⟪ (CX32 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00500 b = win 0 3 b ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00501 : Base 3 → ⟪ (S2 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ S2 ∷ []) ⟫ʷ
wn00501 b = win 0 3 b ((S ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00502 : Base 3 → ⟪ (CK20 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
wn00502 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00503 : Base 3 → ⟪ (CS02 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00503 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00504 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00504 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00505 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00505 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00506 : Base 3 → ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00506 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00507 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00507 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
