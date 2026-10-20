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
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn00409 : ⟪ (CS23 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00409 = win 1 2 complete₃ ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00410 : ⟪ (CS13 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS13 ∷ []) ⟫ʷ
wn00410 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00411 : ⟪ (CX31 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX31 ∷ []) ⟫ʷ
wn00411 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00412 : ⟪ (CS23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS23 ∷ []) ⟫ʷ
wn00412 = win 0 3 complete₃ ((CS ↑) • CS) (CS • (CS ↑)) _ _ Eq.refl
wn00413 : ⟪ (CS23 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
wn00413 = win 0 3 complete₃ ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00414 : ⟪ (CX12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX21 ∷ []) ⟫ʷ
wn00414 = win 3 0 complete₃ ((CX₀₁ ↑) • (Swap ↑)) ((Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00415 : ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ
wn00415 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CZ) (CZ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00416 : ⟪ (CS12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00416 = win 0 3 complete₃ (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) _ _ Eq.refl
wn00417 : ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00417 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00418 : ⟪ (CS12⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00418 = win 0 3 complete₃ ((CS • CS • CS) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00419 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn00419 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00420 : ⟪ (CS13 ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS13 ∷ []) ⟫ʷ
wn00420 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00421 : ⟪ (CS13 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00421 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00422 : ⟪ (CS13 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13 ∷ []) ⟫ʷ
wn00422 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (S ↑ ↑)) ((S ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00423 : ⟪ (CS12 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn00423 = win 3 0 complete₃ ((CS ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00424 : ⟪ (CX20 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX20 ∷ []) ⟫ʷ
wn00424 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00425 : ⟪ (CS12 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00425 = win 3 0 complete₃ ((CS ↑) • (CS • CS • CS)) ((CS • CS • CS) • (CS ↑)) _ _ Eq.refl
wn00426 : ⟪ (CS23 ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS23 ∷ []) ⟫ʷ
wn00426 = win 0 3 complete₃ ((CS ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00427 : ⟪ (CS23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00427 = win 0 3 complete₃ ((CS ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00428 : ⟪ (CS23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS23 ∷ []) ⟫ʷ
wn00428 = win 0 3 complete₃ ((CS ↑) • (S ↑ ↑)) ((S ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00429 : ⟪ (Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff201 ∷ []) ⟫ʷ
wn00429 = win 3 0 complete₃ (Toffᵗ • iI) (iI • Toffᵗ) _ _ Eq.refl
wn00430 : ⟪ (CS23⁻ ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00430 = win 0 3 complete₃ (((CS • CS • CS) ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00431 : ⟪ (S0⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn00431 = win 1 2 complete₃ ((S • S • S) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S • S • S)) _ _ Eq.refl
wn00432 : ⟪ (S3⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S3⁻ ∷ []) ⟫ʷ
wn00432 = win 0 3 complete₃ (((S • S • S) ↑ ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn00433 : ⟪ (CS13 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00433 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00434 : ⟪ (S0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1⁻ ∷ []) ⟫ʷ
wn00434 = win 3 0 complete₃ ((S • S • S) • Swap) (Swap • ((S • S • S) ↑)) _ _ Eq.refl
wn00435 : ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ
wn00435 = win 3 0 complete₃ (iI • Swap) (Swap • iI) _ _ Eq.refl
wn00436 : ⟪ (CS23 ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23 ∷ []) ⟫ʷ
wn00436 = win 0 3 complete₃ ((CS ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00437 : ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ
wn00437 = win 3 0 complete₃ (Swap • iI) (iI • Swap) _ _ Eq.refl
wn00438 : ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ
wn00438 = win 3 0 complete₃ (Toffᵗ • (S • S • S)) ((S • S • S) • Toffᵗ) _ _ Eq.refl
wn00439 : ⟪ (CS23⁻ ∷ ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ S1⁻ ∷ S3⁻ ∷ CS13 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00439 = win 0 3 complete₃ (((CS • CS • CS) ↑) • (iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((iI ↑ ↑) • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00440 : ⟪ (CS23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS23 ∷ []) ⟫ʷ
wn00440 = win 0 3 complete₃ ((CS ↑) • (S ↑)) ((S ↑) • (CS ↑)) _ _ Eq.refl
wn00441 : ⟪ (CS23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00441 = win 0 3 complete₃ ((CS ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (CS ↑)) _ _ Eq.refl
wn00442 : ⟪ (CS23 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS23 ∷ []) ⟫ʷ
wn00442 = win 0 3 complete₃ ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
wn00443 : ⟪ (CS23 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00443 = win 0 3 complete₃ ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00444 : ⟪ (CCZ012 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ012 ∷ []) ⟫ʷ
wn00444 = win 3 0 complete₃ (CCZ • CS) (CS • CCZ) _ _ Eq.refl
wn00445 : ⟪ (S2 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2 ∷ []) ⟫ʷ
wn00445 = win 0 3 complete₃ ((S ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (S ↑)) _ _ Eq.refl
wn00446 : ⟪ (CCZ012 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00446 = win 3 0 complete₃ (CCZ • (CS • CS • CS)) ((CS • CS • CS) • CCZ) _ _ Eq.refl
wn00447 : ⟪ (S2⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S2⁻ ∷ []) ⟫ʷ
wn00447 = win 0 3 complete₃ (((S • S • S) ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00448 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn00448 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00449 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00449 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00450 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00450 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00451 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn00451 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00452 : ⟪ (X1 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ
wn00452 = win 3 0 complete₃ ((X ↑) • (S ↑) • (K ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) _ _ Eq.refl
wn00453 : ⟪ (K1⁻ ∷ S1⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ
wn00453 = win 3 0 complete₃ (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) _ _ Eq.refl
wn00454 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00454 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • Toff) (Toff • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00455 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00455 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00456 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn00456 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00457 : ⟪ (CX21 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CX21 ∷ []) ⟫ʷ
wn00457 = win 0 3 complete₃ (CX₁₀ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CX₁₀) _ _ Eq.refl
wn00458 : ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) ⟫ʷ
wn00458 = win 3 0 complete₃ ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff) _ _ Eq.refl
wn00459 : ⟪ (CS02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00459 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • X) (X • (S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00460 : ⟪ (CS02⁻ ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00460 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀) (CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00461 : ⟪ (CCZ012 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00461 = win 3 0 complete₃ (CCZ • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CZ ↑) • CCZ) _ _ Eq.refl
wn00462 : ⟪ (CS12⁻ ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00462 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00463 : ⟪ (CS02⁻ ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00463 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00464 : ⟪ (S3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S2 ∷ []) ⟫ʷ
wn00464 = win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) _ _ Eq.refl
wn00465 : ⟪ (S2 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ S2 ∷ []) ⟫ʷ
wn00465 = win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00466 : ⟪ (CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00466 = win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) _ _ Eq.refl
wn00467 : ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ
wn00467 = win 3 0 complete₃ ((CZ ↑) • Toff) (Toff • (CZ ↑)) _ _ Eq.refl
wn00468 : ⟪ (CS12⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00468 = win 3 0 complete₃ (((CS • CS • CS) ↑) • Toff) (Toff • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00469 : ⟪ (CS02 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00469 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Toff) (Toff • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) _ _ Eq.refl
wn00470 : ⟪ (S0 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ S0 ∷ []) ⟫ʷ
wn00470 = win 1 2 complete₃ (S • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • S) _ _ Eq.refl
wn00471 : ⟪ (CS13⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn00471 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00472 : ⟪ (Toff102 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff102 ∷ []) ⟫ʷ
wn00472 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • iI) (iI • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00473 : ⟪ (CS13⁻ ∷ ι3 ∷ []) ⟫ʷ ≈ ⟪ (ι3 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00473 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00474 : ⟪ (CS13⁻ ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn00474 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00475 : ⟪ (CS13⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00475 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ ↑)) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00476 : ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ
wn00476 = win 0 3 complete₃ ((S ↑) • (Swap ↑)) ((Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00477 : ⟪ (S2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1 ∷ []) ⟫ʷ
wn00477 = win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) _ _ Eq.refl
wn00478 : ⟪ (CX21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX12 ∷ []) ⟫ʷ
wn00478 = win 3 0 complete₃ ((CX₁₀ ↑) • (Swap ↑)) ((Swap ↑) • (CX₀₁ ↑)) _ _ Eq.refl
wn00479 : ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ
wn00479 = win 3 0 complete₃ ((S ↑) • (Swap ↑)) ((Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00480 : ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ
wn00480 = win 3 0 complete₃ (CK₀₁ • Swap) (Swap • CK₁₀) _ _ Eq.refl
wn00481 : ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ
wn00481 = win 3 0 complete₃ (S • Swap) (Swap • (S ↑)) _ _ Eq.refl
wn00482 : ⟪ (CX32 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00482 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00483 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00483 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00484 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00484 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00485 : ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00485 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00486 : ⟪ (CX32 ∷ X3 ∷ CX31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CX31 ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00486 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00487 : ⟪ (S2 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ S2 ∷ []) ⟫ʷ
wn00487 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00488 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CX21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00488 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00489 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00489 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00490 : ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00490 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS)) ((CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • ((S • S • S) ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • (CS • CS • CS) • (CS • CS • CS) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00491 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00491 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00492 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00492 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00493 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00493 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00494 : ⟪ (CX32 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00494 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00495 : ⟪ (S2 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ S2 ∷ []) ⟫ʷ
wn00495 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00496 : ⟪ (CK20 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
wn00496 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00497 : ⟪ (CS02 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00497 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00498 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00498 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00499 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00499 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00500 : ⟪ (CX32 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CX32 ∷ []) ⟫ʷ
wn00500 = win 0 3 complete₃ ((CX₁₀ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00501 : ⟪ (S2 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ S2 ∷ []) ⟫ʷ
wn00501 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00502 : ⟪ (CK20 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
wn00502 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00503 : ⟪ (CS02 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00503 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00504 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn00504 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn00505 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00505 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00506 : ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00506 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS) (CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00507 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn00507 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
