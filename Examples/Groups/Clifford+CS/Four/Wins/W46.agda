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

module Examples.Groups.Clifford+CS.Four.Wins.W46 where

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

wn02258 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02258 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02259 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02259 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02260 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02260 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02261 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02261 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02262 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CK10 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02262 = win 3 0 complete₃ (S • K) (CS • CK₁₀ • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02263 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CK10⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn02263 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (S ↑ • CK₁₀) • (CS • CS • CS)) _ _ Eq.refl
wn02264 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02264 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) (ε) _ _ Eq.refl
wn02265 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02265 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02266 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02266 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02267 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02267 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02268 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02268 = win 2 1 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02269 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02269 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02270 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02270 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02271 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02271 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02272 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02272 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02273 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02273 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02274 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02274 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02275 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02275 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02276 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02276 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02277 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02277 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02278 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02278 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02279 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02279 = win 1 2 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02280 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02280 = win 1 2 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02281 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02281 = win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02282 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02282 = win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02283 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02283 = win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02284 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02284 = win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02285 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02285 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • S • K) (S • K • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02286 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02286 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02287 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02287 = win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • S • K) (S • K • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02288 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02288 = win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02289 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02289 = win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • S • K) (S • K • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02290 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02290 = win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02291 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn02291 = win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02292 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn02292 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02293 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02293 = win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02294 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02294 = win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02295 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02295 = win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02296 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02296 = win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02297 : ⟪ (Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ CCZ123 ∷ CK32⁻ ∷ []) ⟫ʷ
wn02297 = win 0 3 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((CK₁₀ ↑) • CCZ • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn02298 : ⟪ (CK32 ∷ CCZ123 ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wn02298 = win 0 3 complete₃ ((CK₁₀ ↑) • CCZ • ((S ↑ • CK₁₀) ↑)) ((K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn02299 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ CS01 ∷ CK20⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn02299 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ((Swap ↑ • CK₁₀ • Swap ↑) • CS • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn02300 : ⟪ (CK20 ∷ CS01 ∷ CK20⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
wn02300 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • CS • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (CS • CS • CS)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn02301 : ⟪ (CK23⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02301 = win 0 3 complete₃ (((S • CK₀₁) ↑) • (X ↑)) ((X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02302 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK23⁻ ∷ []) ⟫ʷ
wn02302 = win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑)) ((X ↑) • ((S • CK₀₁) ↑)) _ _ Eq.refl
wn02303 : ⟪ (CK23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02303 = win 0 3 complete₃ ((CK₀₁ ↑) • (X ↑)) ((X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02304 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK23 ∷ []) ⟫ʷ
wn02304 = win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑)) ((X ↑) • (CK₀₁ ↑)) _ _ Eq.refl
wn02305 : ⟪ (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ []) ⟫ʷ
wn02305 = win 0 3 complete₃ ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn02306 : ⟪ (K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02306 = win 0 3 complete₃ ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02307 : ⟪ (CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ CK32 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02307 = win 0 3 complete₃ ((CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑)) (ε) _ _ Eq.refl
wn02308 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02308 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02309 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn02309 = win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02310 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn02310 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02311 : ⟪ (CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02311 = win 3 0 complete₃ ((S ↑ • CK₁₀)) ((K • iI) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02312 : ⟪ (K0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
wn02312 = win 3 0 complete₃ ((K • iI) • (X ↑) • CK₁₀ • (X ↑)) ((S ↑ • CK₁₀)) _ _ Eq.refl
wn02313 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02313 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (K • iI)) ((K • iI) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02314 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02314 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • K) (K • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02315 : ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CK31⁻ ∷ CS13 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02315 = win 0 3 complete₃ ((S • S • S) • (K • iI) • S • S) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02316 : ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CK31 ∷ CS13 ∷ []) ⟫ʷ
wn02316 = win 0 3 complete₃ ((S • S • S) • (S • S • S) • K • S) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02317 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02317 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn02318 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02318 = win 1 2 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02319 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02319 = win 1 2 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02320 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02320 = win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02321 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02321 = win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02322 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02322 = win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑)) ((X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02323 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02323 = win 1 2 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02324 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02324 = win 1 2 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02325 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02325 = win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑)) ((X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02326 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02326 = win 1 2 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02327 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02327 = win 1 2 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02328 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02328 = win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02329 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02329 = win 1 2 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02330 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02330 = win 1 2 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02331 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02331 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02332 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02332 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02333 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02333 = win 1 2 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02334 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02334 = win 1 2 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02335 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02335 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02336 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02336 = win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02337 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02337 = win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02338 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02338 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02339 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02339 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02340 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02340 = win 1 2 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • X) (X • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02341 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02341 = win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02342 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02342 = win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) _ _ Eq.refl
wn02343 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02343 = win 1 2 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • X) (X • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02344 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02344 = win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
