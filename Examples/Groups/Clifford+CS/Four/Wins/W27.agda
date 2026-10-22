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

module Examples.Groups.Clifford+CS.Four.Wins.W27 where

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

wn01332 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
wn01332 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn01333 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
wn01333 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X • (S • CK₀₁) • X) (X • (S • CK₀₁) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn01334 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
wn01334 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X) (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑)) _ _ Eq.refl
wn01335 : Base 3 → ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
wn01335 b = win 3 0 b (X • S • X • S) (iI) _ _ Eq.refl
wn01336 : Base 3 → ⟪ (K0⁻ ∷ CZ02 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
wn01336 b = win 3 0 b ((K • iI) • (Swap ↑ • CZ • Swap ↑) • K) ((Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn01337 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn01337 b = win 0 3 b (CCZ) (CCZ) _ _ Eq.refl
wn01338 : Base 3 → ⟪ (K0 ∷ CX20 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
wn01338 b = win 3 0 b (K • (Swap ↑ • CX₁₀ • Swap ↑) • (K • iI)) ((Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn01339 : Base 3 → ⟪ (K0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01339 b = win 3 0 b ((K • iI) • K) (ε) _ _ Eq.refl
wn01340 : Base 3 → ⟪ (CX23 ∷ CS13 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ CCZ123 ∷ []) ⟫ʷ
wn01340 b = win 0 3 b ((CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑)) ((Swap ↑ • CS • Swap ↑) • CS • CCZ) _ _ Eq.refl
wn01341 : Base 3 → ⟪ (CX23 ∷ CS13⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn01341 b = win 0 3 b ((CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) (CCZ • (CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01342 : Base 3 → ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01342 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) _ _ Eq.refl
wn01343 : Base 3 → ⟪ (CCZ012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ CZ12 ∷ []) ⟫ʷ
wn01343 b = win 3 0 b (CCZ • Toff) (Toff • CCZ • (CZ ↑)) _ _ Eq.refl
wn01344 : Base 3 → ⟪ (CCZ012 ∷ CZ12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
wn01344 b = win 3 0 b (CCZ • (CZ ↑) • Toff) (Toff • CCZ) _ _ Eq.refl
wn01345 : Base 3 → ⟪ (CZ12 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CZ12 ∷ []) ⟫ʷ
wn01345 b = win 3 0 b ((CZ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CZ ↑)) _ _ Eq.refl
wn01346 : Base 3 → ⟪ (CZ12 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CZ12 ∷ []) ⟫ʷ
wn01346 b = win 3 0 b ((CZ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CZ ↑)) _ _ Eq.refl
wn01347 : Base 3 → ⟪ (Toff102 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) ⟫ʷ
wn01347 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI)) ((K ↑) • CCZ • ((K • iI) ↑)) _ _ Eq.refl
wn01348 : Base 3 → ⟪ (K1⁻ ∷ CZ13 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
wn01348 b = win 0 3 b ((K • iI) • (Swap ↑ • CZ • Swap ↑) • K) ((Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn01349 : Base 3 → ⟪ (K1 ∷ CX31 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
wn01349 b = win 0 3 b (K • (Swap ↑ • CX₁₀ • Swap ↑) • (K • iI)) ((Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn01350 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ
wn01350 b = win 0 3 b (ε) (Swap • (Swap ↑) • Swap • Swap • (Swap ↑) • Swap) _ _ Eq.refl
wn01351 : Base 3 → ⟪ (CS02 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS02 ∷ []) ⟫ʷ
wn01351 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01352 : Base 3 → ⟪ (CS02⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01352 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01353 : Base 3 → ⟪ (S2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S2 ∷ []) ⟫ʷ
wn01353 b = win 3 0 b ((S ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (S ↑ ↑)) _ _ Eq.refl
wn01354 : Base 3 → ⟪ (S2⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S2⁻ ∷ []) ⟫ʷ
wn01354 b = win 3 0 b (((S • S • S) ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn01355 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK20 ∷ CK20⁻ ∷ []) ⟫ʷ
wn01355 b = win 3 0 b (ε) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn01356 : Base 3 → ⟪ (CK20⁻ ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01356 b = win 3 0 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (ε) _ _ Eq.refl
wn01357 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ
wn01357 b = win 3 0 b (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01358 : Base 3 → ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01358 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn01359 : Base 3 → ⟪ (X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ Toff102 ∷ []) ⟫ʷ
wn01359 b = win 3 0 b ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01360 : Base 3 → ⟪ (CS02 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ CS02 ∷ []) ⟫ʷ
wn01360 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01361 : Base 3 → ⟪ (CX01 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ
wn01361 b = win 3 0 b (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) _ _ Eq.refl
wn01362 : Base 3 → ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Toff012 ∷ []) ⟫ʷ
wn01362 b = win 3 0 b ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) _ _ Eq.refl
wn01363 : Base 3 → ⟪ (CS02 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn01363 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • CX₁₀) (CX₁₀ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) _ _ Eq.refl
wn01364 : Base 3 → ⟪ (CX10 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
wn01364 b = win 3 0 b (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) _ _ Eq.refl
wn01365 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01365 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) _ _ Eq.refl
wn01366 : Base 3 → ⟪ (CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn01366 b = win 0 3 b ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01367 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ []) ⟫ʷ
wn01367 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01368 : Base 3 → ⟪ (S0 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ S0 ∷ []) ⟫ʷ
wn01368 b = win 3 0 b (S • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • S) _ _ Eq.refl
wn01369 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK31 ∷ CK31⁻ ∷ []) ⟫ʷ
wn01369 b = win 0 3 b (ε) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn01370 : Base 3 → ⟪ (CK31⁻ ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01370 b = win 0 3 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (ε) _ _ Eq.refl
wn01371 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK32 ∷ CK32⁻ ∷ []) ⟫ʷ
wn01371 b = win 0 3 b (ε) ((CK₁₀ ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn01372 : Base 3 → ⟪ (CK32⁻ ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01372 b = win 0 3 b (((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑)) (ε) _ _ Eq.refl
wn01373 : Base 3 → ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Toff123 ∷ []) ⟫ʷ
wn01373 b = win 0 3 b ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) _ _ Eq.refl
wn01374 : Base 3 → ⟪ (CS23 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS23 ∷ []) ⟫ʷ
wn01374 b = win 0 3 b ((CS ↑) • Toff) (Toff • (CS ↑)) _ _ Eq.refl
wn01375 : Base 3 → ⟪ (CX21 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ
wn01375 b = win 0 3 b (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) _ _ Eq.refl
wn01376 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS13 ∷ CS13⁻ ∷ []) ⟫ʷ
wn01376 b = win 0 3 b (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01377 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Toff102 ∷ Toff102 ∷ []) ⟫ʷ
wn01377 b = win 3 0 b (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01378 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS13 ∷ []) ⟫ʷ
wn01378 b = win 0 3 b (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01379 : Base 3 → ⟪ (CS13⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01379 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn01380 : Base 3 → ⟪ (Toff102 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01380 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) _ _ Eq.refl
wn01381 : Base 3 → ⟪ (CS13 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01381 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) _ _ Eq.refl
wn01382 : Base 3 → ⟪ (CS12 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ CS12 ∷ []) ⟫ʷ
wn01382 b = win 3 0 b ((CS ↑) • CX₁₀) (CX₁₀ • (CS ↑)) _ _ Eq.refl
wn01383 : Base 3 → ⟪ (S0⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ S0⁻ ∷ []) ⟫ʷ
wn01383 b = win 3 0 b ((S • S • S) • Toffᵗ) (Toffᵗ • (S • S • S)) _ _ Eq.refl
wn01384 : Base 3 → ⟪ (S2⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S2⁻ ∷ []) ⟫ʷ
wn01384 b = win 3 0 b (((S • S • S) ↑ ↑) • Toff) (Toff • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn01385 : Base 3 → ⟪ (S2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S2 ∷ []) ⟫ʷ
wn01385 b = win 3 0 b ((S ↑ ↑) • Toff) (Toff • (S ↑ ↑)) _ _ Eq.refl
wn01386 : Base 3 → ⟪ (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ
wn01386 b = win 3 0 b (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01387 : Base 3 → ⟪ (CS13 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn01387 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) _ _ Eq.refl
wn01388 : Base 3 → ⟪ (S0 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ S0 ∷ []) ⟫ʷ
wn01388 b = win 3 0 b (S • Toffᵗ) (Toffᵗ • S) _ _ Eq.refl
wn01389 : Base 3 → ⟪ (Toff213 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) ⟫ʷ
wn01389 b = win 0 3 b ((K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01390 : Base 3 → ⟪ (X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ
wn01390 b = win 0 3 b ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) _ _ Eq.refl
wn01391 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ []) ⟫ʷ
wn01391 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01392 : Base 3 → ⟪ (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ []) ⟫ʷ
wn01392 b = win 0 3 b ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑)) ((K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01393 : Base 3 → ⟪ (X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ
wn01393 b = win 0 3 b ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) _ _ Eq.refl
wn01394 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ X3 ∷ []) ⟫ʷ
wn01394 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01395 : Base 3 → ⟪ (X2 ∷ Toff123 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn01395 b = win 0 3 b ((X ↑) • Toff • (X ↑)) ((X ↑) • CK₁₀ • (X ↑) • (Swap ↑ • CZ • Swap ↑) • (CS ↑) • CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn01396 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ CZ13 ∷ CS23 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff123 ∷ X2 ∷ []) ⟫ʷ
wn01396 b = win 0 3 b ((X ↑) • CK₁₀ • (X ↑) • (Swap ↑ • CZ • Swap ↑) • (CS ↑) • CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • Toff • (X ↑)) _ _ Eq.refl
wn01397 : Base 3 → ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ []) ⟫ʷ
wn01397 b = win 0 3 b (Toffᵗ) ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑)) _ _ Eq.refl
wn01398 : Base 3 → ⟪ (CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn01398 b = win 0 3 b ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑)) (Toffᵗ) _ _ Eq.refl
wn01399 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
wn01399 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn01400 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ
wn01400 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) _ _ Eq.refl
wn01401 : Base 3 → ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn01401 b = win 0 3 b ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • CZ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01402 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ CZ12 ∷ CS13 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ
wn01402 b = win 0 3 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • CZ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) _ _ Eq.refl
wn01403 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn01403 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CK₁₀ • CS • CS) _ _ Eq.refl
wn01404 : Base 3 → ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ CX32 ∷ X3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ
wn01404 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) _ _ Eq.refl
wn01405 : Base 3 → ⟪ (X1 ∷ Toff312 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
wn01405 b = win 0 3 b (X • Toffᵗ • X) (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) _ _ Eq.refl
wn01406 : Base 3 → ⟪ (X1 ∷ CK13 ∷ X1 ∷ CZ23 ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff312 ∷ X1 ∷ []) ⟫ʷ
wn01406 b = win 0 3 b (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • Toffᵗ • X) _ _ Eq.refl
wn01407 : Base 3 → ⟪ (CK20 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01407 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01408 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ []) ⟫ʷ
wn01408 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01409 : Base 3 → ⟪ (CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn01409 b = win 0 3 b ((CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01410 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ []) ⟫ʷ
wn01410 b = win 0 3 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑)) _ _ Eq.refl
wn01411 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01411 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01412 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn01412 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01413 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn01413 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01414 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn01414 b = win 1 2 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01415 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn01415 b = win 0 3 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01416 : Base 3 → ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn01416 b = win 3 0 b (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01417 : Base 3 → ⟪ (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
wn01417 b = win 3 0 b (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01418 : Base 3 → ⟪ (S1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ S1 ∷ []) ⟫ʷ
wn01418 b = win 3 0 b ((S ↑) • Toff) (Toff • (S ↑)) _ _ Eq.refl
wn01419 : Base 3 → ⟪ (X1 ∷ CX10 ∷ X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) ⟫ʷ
wn01419 b = win 3 0 b ((X ↑) • CX₁₀ • (X ↑) • X) (X • (X ↑) • CX₁₀ • (X ↑)) _ _ Eq.refl
wn01420 : Base 3 → ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ []) ⟫ʷ
wn01420 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS) (CS • CS • CK₁₀ • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
