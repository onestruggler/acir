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

module Examples.Groups.Clifford+CS.Four.Wins.W44 where

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

wn02080 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02080 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • K • S • S • K) (K • S • S • K • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02081 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02081 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI)) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02082 : Base 3 → ⟪ (CK13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
wn02082 b = win 0 3 b ((Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) _ _ Eq.refl
wn02083 : Base 3 → ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK13⁻ ∷ []) ⟫ʷ
wn02083 b = win 0 3 b (X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X) (X • (Swap ↑ • (S • CK₀₁) • Swap ↑)) _ _ Eq.refl
wn02084 : Base 3 → ⟪ (CK13 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
wn02084 b = win 0 3 b ((Swap ↑ • CK₀₁ • Swap ↑) • X) (X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X) _ _ Eq.refl
wn02085 : Base 3 → ⟪ (X1 ∷ CK13 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK13 ∷ []) ⟫ʷ
wn02085 b = win 0 3 b (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X) (X • (Swap ↑ • CK₀₁ • Swap ↑)) _ _ Eq.refl
wn02086 : Base 3 → ⟪ (CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn02086 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02087 : Base 3 → ⟪ (X2 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02087 b = win 3 0 b ((X ↑ ↑) • K • (Swap ↑ • CS • Swap ↑) • (K • iI) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02088 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X2 ∷ []) ⟫ʷ
wn02088 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • K • (Swap ↑ • CS • Swap ↑) • (K • iI) • (X ↑ ↑)) _ _ Eq.refl
wn02089 : Base 3 → ⟪ (X2 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02089 b = win 3 0 b ((X ↑ ↑) • K • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (K • iI) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02090 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ X2 ∷ []) ⟫ʷ
wn02090 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • K • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (K • iI) • (X ↑ ↑)) _ _ Eq.refl
wn02091 : Base 3 → ⟪ (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ
wn02091 b = win 3 0 b (K • (K • iI) • S • K) (S • K) _ _ Eq.refl
wn02092 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02092 b = win 3 0 b ((K • iI) • (S • S • S) • K • (K • iI)) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02093 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ
wn02093 b = win 3 0 b (S • K) (S • K) _ _ Eq.refl
wn02094 : Base 3 → ⟪ (K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02094 b = win 3 0 b ((K • iI)) ((K • iI) • (S • S • S) • S) _ _ Eq.refl
wn02095 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02095 b = win 3 0 b ((K • iI) • S • K) ((S • S • S) • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02096 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02096 b = win 3 0 b ((K • iI) • (S • S • S)) (S • K • S • (K • iI)) _ _ Eq.refl
wn02097 : Base 3 → ⟪ (S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02097 b = win 3 0 b (S • (S • S • S) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S)) _ _ Eq.refl
wn02098 : Base 3 → ⟪ (S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn02098 b = win 3 0 b (S • K • S) (S • K • S) _ _ Eq.refl
wn02099 : Base 3 → ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CK20 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02099 b = win 3 0 b (S • K) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02100 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn02100 b = win 3 0 b ((K • iI) • (S • S • S)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn02101 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02101 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn02102 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02102 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02103 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn02103 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02104 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02104 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02105 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02105 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02106 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn02106 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02107 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02107 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02108 : Base 3 → ⟪ (S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CK31 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02108 b = win 0 3 b (S • K) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02109 : Base 3 → ⟪ (K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn02109 b = win 0 3 b ((K • iI) • (S • S • S)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn02110 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02110 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn02111 : Base 3 → ⟪ (CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02111 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02112 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ []) ⟫ʷ
wn02112 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02113 : Base 3 → ⟪ (CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02113 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02114 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ []) ⟫ʷ
wn02114 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn02115 : Base 3 → ⟪ (S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CK21 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn02115 b = win 3 0 b ((S ↑) • (K ↑)) ((CS ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02116 : Base 3 → ⟪ (K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CK21⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn02116 b = win 3 0 b (((K • iI) ↑) • ((S • S • S) ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn02117 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02117 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn02118 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02118 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02119 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02119 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02120 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02120 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02121 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02121 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02122 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02122 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02123 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02123 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02124 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02124 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02125 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02125 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02126 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02126 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02127 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02127 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02128 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK21 ∷ CK21⁻ ∷ []) ⟫ʷ
wn02128 b = win 3 0 b (ε) ((CK₁₀ ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn02129 : Base 3 → ⟪ (CK21⁻ ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02129 b = win 3 0 b (((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑)) (ε) _ _ Eq.refl
wn02130 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02130 b = win 3 0 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02131 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn02131 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02132 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn02132 b = win 3 0 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02133 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn02133 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02134 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn02134 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02135 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn02135 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02136 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02136 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02137 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02137 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02138 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02138 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02139 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02139 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02140 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02140 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02141 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02141 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02142 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK10 ∷ CK10⁻ ∷ []) ⟫ʷ
wn02142 b = win 3 0 b (ε) (CK₁₀ • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02143 : Base 3 → ⟪ (CK10⁻ ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02143 b = win 3 0 b ((S ↑ • CK₁₀) • CK₁₀) (ε) _ _ Eq.refl
wn02144 : Base 3 → ⟪ (X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ []) ⟫ʷ
wn02144 b = win 3 0 b ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • S • K) (S • K • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02145 : Base 3 → ⟪ (X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12 ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ []) ⟫ʷ
wn02145 b = win 3 0 b ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02146 : Base 3 → ⟪ (X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) ⟫ʷ
wn02146 b = win 3 0 b ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • S • K) (S • K • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02147 : Base 3 → ⟪ (X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) ⟫ʷ
wn02147 b = win 3 0 b ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02148 : Base 3 → ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02148 b = win 0 3 b ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02149 : Base 3 → ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02149 b = win 0 3 b ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02150 : Base 3 → ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02150 b = win 0 3 b ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02151 : Base 3 → ⟪ (X2 ∷ CK23 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02151 b = win 0 3 b ((X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02152 : Base 3 → ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02152 b = win 0 3 b ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02153 : Base 3 → ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02153 b = win 0 3 b ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02154 : Base 3 → ⟪ (CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02154 b = win 0 3 b ((CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02155 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ []) ⟫ʷ
wn02155 b = win 0 3 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn02156 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02156 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02157 : Base 3 → ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02157 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02158 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02158 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02159 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02159 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02160 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02160 b = win 3 0 b ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02161 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02161 b = win 2 1 b ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02162 : Base 3 → ⟪ (X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02162 b = win 3 0 b ((X ↑) • CK₁₀ • (X ↑)) ((X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02163 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02163 b = win 3 0 b ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02164 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn02164 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02165 : Base 3 → ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02165 b = win 1 2 b ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02166 : Base 3 → ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02166 b = win 1 2 b ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02167 : Base 3 → ⟪ (X2 ∷ CK23 ∷ X2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02167 b = win 1 2 b ((X ↑) • (CK₀₁ ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02168 : Base 3 → ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02168 b = win 1 2 b ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02169 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02169 b = win 1 2 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02170 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02170 b = win 0 3 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
