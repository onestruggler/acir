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
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn02572 : ⟪ (S0 ∷ S0 ∷ X0 ∷ X1 ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
wn02572 = win 3 0 complete₃ (S • S • X • (X ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑ ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • S • Toff • (S • S • S) • X • (X ↑)) (X) _ _ Eq.refl
wn02573 : ⟪ (S2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ S1⁻ ∷ []) ⟫ʷ
wn02573 = win 3 0 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn02574 : ⟪ (K2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1⁻ ∷ []) ⟫ʷ
wn02574 = win 3 0 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn02575 : ⟪ (S1 ∷ S1 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ X0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
wn02575 = win 3 0 complete₃ ((S ↑) • (S ↑) • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑) • (K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • X • (X ↑)) ((X ↑)) _ _ Eq.refl
wn02576 : ⟪ (S2 ∷ S2 ∷ X0 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
wn02576 = win 3 0 complete₃ ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑)) _ _ Eq.refl
wn02577 : ⟪ (S2 ∷ S2 ∷ X0 ∷ X1 ∷ X2 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ X1 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X0 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
wn02577 = win 3 0 complete₃ ((S ↑ ↑) • (S ↑ ↑) • X • (X ↑) • (X ↑ ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (X ↑) • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • X • (CS • CS • CS) • (S ↑ ↑) • Toffᵗ • ((S • S • S) ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑)) _ _ Eq.refl
wn02578 : ⟪ [] ⟫ʷ ≈ ⟪ (S1 ∷ S1⁻ ∷ []) ⟫ʷ
wn02578 = win 3 0 complete₃ (ε) ((S ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn02579 : ⟪ [] ⟫ʷ ≈ ⟪ (K1 ∷ K1⁻ ∷ []) ⟫ʷ
wn02579 = win 3 0 complete₃ (ε) ((K ↑) • ((K • iI) ↑)) _ _ Eq.refl
wn02580 : ⟪ [] ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1 ∷ []) ⟫ʷ
wn02580 = win 3 0 complete₃ (ε) (((S • S • S) ↑) • (S ↑)) _ _ Eq.refl
wn02581 : ⟪ (S1⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02581 = win 3 0 complete₃ (((S • S • S) ↑) • (S ↑)) (ε) _ _ Eq.refl
wn02582 : ⟪ (K1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02582 = win 3 0 complete₃ ((K ↑) • ((K • iI) ↑)) (ε) _ _ Eq.refl
wn02583 : ⟪ (S1 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02583 = win 3 0 complete₃ ((S ↑) • ((S • S • S) ↑)) (ε) _ _ Eq.refl
wn02584 : ⟪ (CX10 ∷ CZ01 ∷ CZ01 ∷ CX01 ∷ CX10 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw01 ∷ []) ⟫ʷ
wn02584 = win 3 0 complete₃ (CX₁₀ • CZ • CZ • CX₀₁ • CX₁₀ • CZ) (CZ • Swap) _ _ Eq.refl
