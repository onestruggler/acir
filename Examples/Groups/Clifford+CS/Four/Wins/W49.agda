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

module Examples.Groups.Clifford+CS.Four.Wins.W49 where

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

wn02572 : Base 3 → ⟪ (S0 ∷ S0 ∷ X0 ∷ X1 ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02572 b = win 3 0 b (S • S • X • (X ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • X • (X ↑)) (X) _ _ Eq.refl
wn02573 : Base 3 → ⟪ (S2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1⁻ ∷ []) ⟫ʷ
wn02573 b = win 3 0 b (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn02574 : Base 3 → ⟪ (K2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1⁻ ∷ []) ⟫ʷ
wn02574 b = win 3 0 b (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn02575 : Base 3 → ⟪ (S1 ∷ S1 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
wn02575 b = win 3 0 b ((S ↑) • (S ↑) • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑)) ((X ↑)) _ _ Eq.refl
wn02576 : Base 3 → ⟪ (S2 ∷ S2 ∷ X0 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
wn02576 b = win 3 0 b ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑)) _ _ Eq.refl
wn02577 : Base 3 → ⟪ (S2 ∷ S2 ∷ X0 ∷ X1 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
wn02577 b = win 3 0 b ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑) • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑)) _ _ Eq.refl
wn02578 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S1 ∷ S1⁻ ∷ []) ⟫ʷ
wn02578 b = win 3 0 b (ε) ((S ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn02579 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K1 ∷ K1⁻ ∷ []) ⟫ʷ
wn02579 b = win 3 0 b (ε) ((K ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn02580 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1 ∷ []) ⟫ʷ
wn02580 b = win 3 0 b (ε) (((S • S • S) ↑) • (S ↑)) _ _ Eq.refl
wn02581 : Base 3 → ⟪ (S1⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02581 b = win 3 0 b (((S • S • S) ↑) • (S ↑)) (ε) _ _ Eq.refl
wn02582 : Base 3 → ⟪ (K1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02582 b = win 3 0 b ((K ↑) • ((K • iI) ↑)) (ε) _ _ Eq.refl
wn02583 : Base 3 → ⟪ (S1 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02583 b = win 3 0 b ((S ↑) • ((S • S • S) ↑)) (ε) _ _ Eq.refl
wn02584 : Base 3 → ⟪ (CX10 ∷ CZ01 ∷ CZ01 ∷ CX01 ∷ CX10 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw01 ∷ []) ⟫ʷ
wn02584 b = win 3 0 b (CX₁₀ • CZ • CZ • CX₀₁ • CX₁₀ • CZ) (CZ • Swap) _ _ Eq.refl
