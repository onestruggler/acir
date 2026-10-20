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

module Examples.Groups.Clifford+CS.Four.Wins.W35 where

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

wn01689 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn01689 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01690 : ⟪ (X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK12 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) ⟫ʷ
wn01690 = win 0 3 complete₃ (X • (K ↑ • CCZ • K ↑ • iI) • X) (X • CK₀₁ • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (S • CK₀₁) • X) _ _ Eq.refl
wn01691 : ⟪ (X1 ∷ CK12 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff213 ∷ X1 ∷ []) ⟫ʷ
wn01691 = win 0 3 complete₃ (X • CK₀₁ • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (S • CK₀₁) • X) (X • (K ↑ • CCZ • K ↑ • iI) • X) _ _ Eq.refl
wn01692 : ⟪ [] ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CK20 ∷ []) ⟫ʷ
wn01692 = win 3 0 complete₃ (ε) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01693 : ⟪ [] ⟫ʷ ≈ ⟪ (S3⁻ ∷ S3 ∷ []) ⟫ʷ
wn01693 = win 0 3 complete₃ (ε) (((S • S • S) ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn01694 : ⟪ [] ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS01 ∷ []) ⟫ʷ
wn01694 = win 3 0 complete₃ (ε) ((CS • CS • CS) • CS) _ _ Eq.refl
wn01695 : ⟪ [] ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CK10 ∷ []) ⟫ʷ
wn01695 = win 3 0 complete₃ (ε) ((S ↑ • CK₁₀) • CK₁₀) _ _ Eq.refl
wn01696 : ⟪ (CK20 ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01696 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (ε) _ _ Eq.refl
wn01697 : ⟪ (CX13 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01697 = win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) (ε) _ _ Eq.refl
wn01698 : ⟪ (CS01 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01698 = win 3 0 complete₃ (CS • (CS • CS • CS)) (ε) _ _ Eq.refl
wn01699 : ⟪ (CK10 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01699 = win 3 0 complete₃ (CK₁₀ • (S ↑ • CK₁₀)) (ε) _ _ Eq.refl
wn01700 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01700 = win 3 0 complete₃ (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01701 : ⟪ (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) ⟫ʷ
wn01701 = win 3 0 complete₃ (CX₁₀ • CZ • (X ↑) • CX₀₁ • CZ • (X ↑)) (Swap • X • (X ↑) • CX₁₀ • (X ↑)) _ _ Eq.refl
wn01702 : ⟪ (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) ⟫ʷ
wn01702 = win 3 0 complete₃ (Swap • X • (X ↑) • CX₁₀ • (X ↑)) (CX₁₀ • CZ • (X ↑) • CX₀₁ • CZ • (X ↑)) _ _ Eq.refl
wn01703 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn01703 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (S • S • S) • K • K • K • K) ((S • S • S) • K • K • K • K • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn01704 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn01704 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • (K • iI) • (K • iI) • S) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn01705 : ⟪ [] ⟫ʷ ≈ ⟪ (CX12 ∷ CX12 ∷ []) ⟫ʷ
wn01705 = win 3 0 complete₃ (ε) ((CX₀₁ ↑) • (CX₀₁ ↑)) _ _ Eq.refl
wn01706 : ⟪ [] ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2 ∷ []) ⟫ʷ
wn01706 = win 3 0 complete₃ (ε) (((S • S • S) ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn01707 : ⟪ (CX12 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01707 = win 3 0 complete₃ ((CX₀₁ ↑) • (CX₀₁ ↑)) (ε) _ _ Eq.refl
wn01708 : ⟪ (S2 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01708 = win 3 0 complete₃ ((S ↑ ↑) • ((S • S • S) ↑ ↑)) (ε) _ _ Eq.refl
wn01709 : ⟪ (CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01709 = win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ((K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01710 : ⟪ (K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
wn01710 = win 3 0 complete₃ ((K • iI)) ((K • iI)) _ _ Eq.refl
wn01711 : ⟪ (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
wn01711 = win 3 0 complete₃ ((K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn01712 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01712 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K • iI)) ((K • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01713 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn01713 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • K) (K • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01714 : ⟪ (CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn01714 = win 3 0 complete₃ (CS • (X ↑)) ((X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn01715 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ []) ⟫ʷ
wn01715 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑)) ((X ↑) • CS) _ _ Eq.refl
wn01716 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn01716 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • CS • CS • CS • (S ↑) • CK₁₀ • CS • CS • CS • CS • CS • CS) (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01717 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
wn01717 = win 3 0 complete₃ (CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • CS • CS • CS • (S ↑) • CK₁₀ • CS • CS • CS • CS • CS • CS) _ _ Eq.refl
wn01718 : ⟪ (CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CK20 ∷ []) ⟫ʷ
wn01718 = win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ((S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01719 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01719 = win 3 0 complete₃ ((X ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑)) ((X ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑) • (X ↑) • (CX₀₁ ↑) • (X ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑) • (CX₀₁ ↑) • (X ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01720 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ []) ⟫ʷ
wn01720 = win 3 0 complete₃ ((X ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑) • (X ↑) • (CX₀₁ ↑) • (X ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑) • (CX₀₁ ↑) • (X ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ((X ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑)) _ _ Eq.refl
wn01721 : ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ
wn01721 = win 3 0 complete₃ (X • Toffᵗ • X) (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) _ _ Eq.refl
wn01722 : ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ
wn01722 = win 3 0 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • Toffᵗ • X) _ _ Eq.refl
wn01723 : ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ
wn01723 = win 3 0 complete₃ (X • Toffᵗ • X) (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • (Swap ↑ • CS • Swap ↑) • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) _ _ Eq.refl
wn01724 : ⟪ (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ
wn01724 = win 3 0 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • (Swap ↑ • CS • Swap ↑) • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • Toffᵗ • X) _ _ Eq.refl
wn01725 : ⟪ (S1 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
wn01725 = win 3 0 complete₃ ((S ↑) • CK₁₀) ((S ↑ • CK₁₀)) _ _ Eq.refl
wn01726 : ⟪ [] ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn01726 = win 3 0 complete₃ (ε) ((S • S • S) • S) _ _ Eq.refl
wn01727 : ⟪ (S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
wn01727 = win 3 0 complete₃ (S) (S) _ _ Eq.refl
wn01728 : ⟪ (S0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01728 = win 3 0 complete₃ (S • (S • S • S)) (ε) _ _ Eq.refl
wn01729 : ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01729 = win 3 0 complete₃ (S • S • (K • iI) • (S • S • S)) (S • S • (K • iI) • S • S • S) _ _ Eq.refl
wn01730 : ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn01730 = win 3 0 complete₃ (S • K • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (S • S • S) • K • (S • S • S) • (S • S • S)) _ _ Eq.refl
wn01731 : ⟪ (K1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K0⁻ ∷ []) ⟫ʷ
wn01731 = win 3 0 complete₃ (((K • iI) ↑) • Swap) (Swap • (K • iI)) _ _ Eq.refl
wn01732 : ⟪ [] ⟫ʷ ≈ ⟪ (S0 ∷ S0⁻ ∷ []) ⟫ʷ
wn01732 = win 3 0 complete₃ (ε) (S • (S • S • S)) _ _ Eq.refl
wn01733 : ⟪ (S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01733 = win 3 0 complete₃ ((S • S • S)) (S • S • S) _ _ Eq.refl
wn01734 : ⟪ (S0 ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01734 = win 3 0 complete₃ (S • S • S • S) (ε) _ _ Eq.refl
wn01735 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn01735 = win 3 0 complete₃ (S • K) (S • (K • iI) • (S • S • S) • S • K • K) _ _ Eq.refl
wn01736 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ
wn01736 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((K • iI) • (K • iI) • (S • S • S) • S • K • (S • S • S)) _ _ Eq.refl
wn01737 : ⟪ (S0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ ι ∷ ι ∷ ι ∷ []) ⟫ʷ
wn01737 = win 3 0 complete₃ (S • K • K) (S • iI • iI • iI) _ _ Eq.refl
wn01738 : ⟪ (ι ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ ι ∷ []) ⟫ʷ
wn01738 = win 3 0 complete₃ (iI • Toff) (Toff • iI) _ _ Eq.refl
wn01739 : ⟪ (ι ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ ι ∷ []) ⟫ʷ
wn01739 = win 3 0 complete₃ (iI • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • iI) _ _ Eq.refl
wn01740 : ⟪ (ι ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ ι ∷ []) ⟫ʷ
wn01740 = win 3 0 complete₃ (iI • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • iI) _ _ Eq.refl
wn01741 : ⟪ (S0 ∷ ι ∷ ι ∷ ι ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01741 = win 3 0 complete₃ (S • iI • iI • iI • (K • iI) • (K • iI) • (S • S • S)) (ε) _ _ Eq.refl
wn01742 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01742 = win 3 0 complete₃ (S • K) (S • K • S • S • S • S) _ _ Eq.refl
wn01743 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn01743 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((S • S • S) • (S • S • S) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn01744 : ⟪ (S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ []) ⟫ʷ
wn01744 = win 3 0 complete₃ (S • S) (S • S) _ _ Eq.refl
wn01745 : ⟪ (S0 ∷ S0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01745 = win 3 0 complete₃ (S • S • (S • S • S) • (S • S • S)) (ε) _ _ Eq.refl
wn01746 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn01746 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((K • iI) • S • S • S) _ _ Eq.refl
wn01747 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn01747 = win 3 0 complete₃ (S • K) ((S • S • S) • (S • S • S) • (S • S • S) • K) _ _ Eq.refl
wn01748 : ⟪ (CS02⁻ ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01748 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01749 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn01749 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01750 : ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CZ12 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ
wn01750 = win 0 3 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((K ↑) • CZ • CCZ • ((K • iI) ↑)) _ _ Eq.refl
wn01751 : ⟪ (Toff213 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ
wn01751 = win 0 3 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((K ↑) • CCZ • ((K • iI) ↑)) _ _ Eq.refl
wn01752 : ⟪ (K2⁻ ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01752 = win 3 0 complete₃ (((K • iI) ↑ ↑) • (K ↑ ↑)) (ε) _ _ Eq.refl
wn01753 : ⟪ [] ⟫ʷ ≈ ⟪ (K2⁻ ∷ K2 ∷ []) ⟫ʷ
wn01753 = win 3 0 complete₃ (ε) (((K • iI) ↑ ↑) • (K ↑ ↑)) _ _ Eq.refl
wn01754 : ⟪ (K2 ∷ CZ12 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ
wn01754 = win 0 3 complete₃ ((K ↑) • CZ • CCZ • ((K • iI) ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) _ _ Eq.refl
wn01755 : ⟪ (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wn01755 = win 0 3 complete₃ ((K ↑) • CCZ • ((K • iI) ↑)) ((K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01756 : ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ Toff123 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01756 = win 0 3 complete₃ (Toff) ((X ↑) • (X ↑) • Toff • (X ↑) • (X ↑)) _ _ Eq.refl
wn01757 : ⟪ (X2 ∷ X2 ∷ X3 ∷ Toff123 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ X2 ∷ []) ⟫ʷ
wn01757 = win 0 3 complete₃ ((X ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (X ↑)) _ _ Eq.refl
wn01758 : ⟪ (X2 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff123 ∷ X2 ∷ X3 ∷ X2 ∷ []) ⟫ʷ
wn01758 = win 0 3 complete₃ ((X ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (X ↑)) _ _ Eq.refl
wn01759 : ⟪ (X2 ∷ X2 ∷ Toff123 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn01759 = win 0 3 complete₃ ((X ↑) • (X ↑) • Toff • (X ↑) • (X ↑)) (Toff) _ _ Eq.refl
wn01760 : ⟪ (X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ []) ⟫ʷ
wn01760 = win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) _ _ Eq.refl
wn01761 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01761 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01762 : ⟪ (X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ []) ⟫ʷ
wn01762 = win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) _ _ Eq.refl
wn01763 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01763 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01764 : ⟪ (X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ []) ⟫ʷ
wn01764 = win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • CK₀₁ • S • CK₀₁ • S • CS • CS • CS • CK₀₁ • S • CS • CS • CS • CS • CS • CS • (Swap ↑ • CX₁₀ • Swap ↑) • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (X ↑ ↑)) ((CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • CK₀₁ • S • CK₀₁ • S • CS • CS • CS • CK₀₁ • S • CS • CS • CS • CS • CS • CS • (Swap ↑ • CX₁₀ • Swap ↑) • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (X ↑ ↑)) _ _ Eq.refl
wn01765 : ⟪ (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX20 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X2 ∷ X2 ∷ []) ⟫ʷ
wn01765 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • CK₀₁ • S • CK₀₁ • S • CS • CS • CS • CK₀₁ • S • CS • CS • CS • CS • CS • CS • (Swap ↑ • CX₁₀ • Swap ↑) • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁) ((X ↑ ↑) • (CS ↑) • (CS ↑) • (CK₁₀ ↑) • (CS ↑) • (CK₁₀ ↑) • (CK₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • CK₀₁ • S • CK₀₁ • S • CS • CS • CS • CK₀₁ • S • CS • CS • CS • CS • CS • CS • (Swap ↑ • CX₁₀ • Swap ↑) • CS • CS • CK₀₁ • CS • CK₀₁ • CK₀₁ • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01766 : ⟪ (X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ
wn01766 = win 0 3 complete₃ ((X ↑) • Toffᵗ • (X ↑)) ((K ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • CCZ • ((K • iI) ↑ ↑)) _ _ Eq.refl
wn01767 : ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ
wn01767 = win 0 3 complete₃ (Toffᵗ) ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) _ _ Eq.refl
wn01768 : ⟪ (K3⁻ ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01768 = win 0 3 complete₃ (((K • iI) ↑ ↑) • (K ↑ ↑)) (ε) _ _ Eq.refl
wn01769 : ⟪ [] ⟫ʷ ≈ ⟪ (K3⁻ ∷ K3 ∷ []) ⟫ʷ
wn01769 = win 0 3 complete₃ (ε) (((K • iI) ↑ ↑) • (K ↑ ↑)) _ _ Eq.refl
wn01770 : ⟪ (K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ
wn01770 = win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • CCZ • ((K • iI) ↑ ↑)) ((X ↑) • Toffᵗ • (X ↑)) _ _ Eq.refl
wn01771 : ⟪ (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn01771 = win 0 3 complete₃ ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) (Toffᵗ) _ _ Eq.refl
