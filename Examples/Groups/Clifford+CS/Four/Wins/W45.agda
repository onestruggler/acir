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

module Examples.Groups.Clifford+CS.Four.Wins.W45 where

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

wn02171 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02171 = win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • K • S • S • (K • iI)) (K • S • S • (K • iI) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02172 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
wn02172 = win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) _ _ Eq.refl
wn02173 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02173 = win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • K • S • S • (K • iI)) (K • S • S • (K • iI) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02174 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
wn02174 = win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) _ _ Eq.refl
wn02175 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02175 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K • iI) • (K • iI)) ((K • iI) • (K • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02176 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02176 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • K • K) (K • K • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02177 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02177 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • S • S • (K • iI) • S) (S • S • (K • iI) • S • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02178 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02178 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • K • (S • S • S) • (S • S • S)) ((S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02179 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02179 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S • (K • iI)) ((S • S • S) • (K • iI) • S • S • (K • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02180 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02180 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • K • (S • S • S) • (S • S • S) • K • S) (K • (S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02181 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02181 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • K • S • S) ((S • S • S) • K • S • S • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02182 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02182 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • (K • iI) • S) ((S • S • S) • (S • S • S) • (K • iI) • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02183 : ⟪ (K0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02183 = win 3 0 complete₃ ((K • iI) • K • S • S • (K • iI)) (S • S • (K • iI)) _ _ Eq.refl
wn02184 : ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02184 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02185 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02185 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • S • (K • iI)) (S • (K • iI) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02186 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02186 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • K • (S • S • S)) (K • (S • S • S) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02187 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02187 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • S • (K • iI)) ((K • iI) • S • (K • iI) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02188 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02188 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • K • (S • S • S) • K) (K • (S • S • S) • K • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02189 : ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02189 = win 3 0 complete₃ ((K • iI) • S • (K • iI) • S • (K • iI)) ((S • S • S) • K • K • K • K) _ _ Eq.refl
wn02190 : ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02190 = win 3 0 complete₃ (K • (S • S • S) • K • (S • S • S)) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • S • (K • iI)) _ _ Eq.refl
wn02191 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02191 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S • (K • iI) • S • (K • iI) • (S • S • S)) (S • (K • iI) • S • (K • iI) • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02192 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02192 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • S • K • (S • S • S) • K • (S • S • S)) (S • K • (S • S • S) • K • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02193 : ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02193 = win 3 0 complete₃ (K • S • S • (K • iI) • S • (K • iI) • (S • S • S)) ((S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) _ _ Eq.refl
wn02194 : ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02194 = win 3 0 complete₃ (S • K • (S • S • S) • K • (S • S • S) • (S • S • S)) (K • K • (S • S • S) • K • S • K) _ _ Eq.refl
wn02195 : ⟪ (K0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02195 = win 3 0 complete₃ (K • (S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) (S • (K • iI) • S • S) _ _ Eq.refl
wn02196 : ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02196 = win 3 0 complete₃ (K • K • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • (S • S • S) • K) _ _ Eq.refl
wn02197 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02197 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • S • (K • iI) • S • S) (S • (K • iI) • S • S • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02198 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02198 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • (S • S • S)) ((S • S • S) • (S • S • S) • K • (S • S • S) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02199 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02199 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • K • S • S • K) ((S • S • S) • K • S • S • K • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02200 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02200 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02201 : ⟪ (K0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02201 = win 3 0 complete₃ (K • K • S • S • K) (S • S • K • K • K) _ _ Eq.refl
wn02202 : ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02202 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S) • (K • iI)) ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S) • K) _ _ Eq.refl
wn02203 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02203 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • K • (S • S • S) • K • K) ((S • S • S) • K • (S • S • S) • K • K • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02204 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02204 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (K • iI) • (K • iI) • S • (K • iI) • S) ((K • iI) • (K • iI) • S • (K • iI) • S • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02205 : ⟪ (CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02205 = win 3 0 complete₃ (CK₁₀ • (X ↑)) ((X ↑) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02206 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ []) ⟫ʷ
wn02206 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑)) ((X ↑) • CK₁₀) _ _ Eq.refl
wn02207 : ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ CCZ123 ∷ CK13⁻ ∷ []) ⟫ʷ
wn02207 = win 0 3 complete₃ (Toffᵗ) ((Swap ↑ • CK₀₁ • Swap ↑) • CCZ • (Swap ↑ • (S • CK₀₁) • Swap ↑)) _ _ Eq.refl
wn02208 : ⟪ (CK13 ∷ CCZ123 ∷ CK13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn02208 = win 0 3 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • CCZ • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (Toffᵗ) _ _ Eq.refl
wn02209 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02209 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (K • iI)) ((K • iI) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02210 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02210 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • K) (K • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02211 : ⟪ (CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
wn02211 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn02212 : ⟪ (CS02⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
wn02212 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn02213 : ⟪ (CS02 ∷ CZ02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02213 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn02214 : ⟪ (X0 ∷ Toff012 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn02214 = win 3 0 complete₃ (X • Toff • X) (Toff) _ _ Eq.refl
wn02215 : ⟪ (X0 ∷ CS02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn02215 = win 3 0 complete₃ (X • (Swap ↑ • CS • Swap ↑) • X) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn02216 : ⟪ (X0 ∷ CS02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S2⁻ ∷ []) ⟫ʷ
wn02216 = win 3 0 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn02217 : ⟪ (S2 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S2 ∷ []) ⟫ʷ
wn02217 = win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn02218 : ⟪ (S2 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S2 ∷ []) ⟫ʷ
wn02218 = win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn02219 : ⟪ (S2 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wn02219 = win 3 0 complete₃ ((S ↑ ↑) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02220 : ⟪ (S2⁻ ∷ S2 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn02220 = win 3 0 complete₃ (((S • S • S) ↑ ↑) • (S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn02221 : ⟪ (X0 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ X0 ∷ []) ⟫ʷ
wn02221 = win 3 0 complete₃ (X • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • X) _ _ Eq.refl
wn02222 : ⟪ (S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ
wn02222 = win 3 0 complete₃ (S • K) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02223 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn02223 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02224 : ⟪ (CS02 ∷ CK20 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02224 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) _ _ Eq.refl
wn02225 : ⟪ (S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CK31 ∷ []) ⟫ʷ
wn02225 = win 0 3 complete₃ (S • K) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02226 : ⟪ (K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02226 = win 0 3 complete₃ ((K • iI) • (S • S • S)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02227 : ⟪ (CS13 ∷ CK31 ∷ CK31⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02227 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) _ _ Eq.refl
wn02228 : ⟪ (S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ CS12 ∷ CK21 ∷ []) ⟫ʷ
wn02228 = win 3 0 complete₃ ((S ↑) • (K ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (CS ↑) • (CK₁₀ ↑)) _ _ Eq.refl
wn02229 : ⟪ (K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ CS12⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn02229 = win 3 0 complete₃ (((K • iI) ↑) • ((S • S • S) ↑)) (((S ↑ • CK₁₀) ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02230 : ⟪ (CS12 ∷ CK21 ∷ CK21⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02230 = win 3 0 complete₃ ((CS ↑) • (CK₁₀ ↑) • ((S ↑ • CK₁₀) ↑) • ((CS • CS • CS) ↑)) (ε) _ _ Eq.refl
wn02231 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02231 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S • K) (S • K • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02232 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02232 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02233 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02233 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S • S • K) (S • S • K • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02234 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02234 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (S • S • S) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02235 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn02235 = win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02236 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn02236 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02237 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ S1 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn02237 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02238 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02238 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02239 : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
wn02239 = win 3 0 complete₃ ((S • S • S) • (K • iI) • S • S) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn02240 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02240 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02241 : ⟪ (CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02241 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn02242 : ⟪ (CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02242 = win 0 3 complete₃ (((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02243 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ []) ⟫ʷ
wn02243 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn02244 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02244 = win 1 2 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02245 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02245 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02246 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02246 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02247 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02247 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02248 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02248 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02249 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn02249 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02250 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn02250 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02251 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02251 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02252 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02252 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02253 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02253 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02254 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn02254 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02255 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02255 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02256 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn02256 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02257 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02257 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
