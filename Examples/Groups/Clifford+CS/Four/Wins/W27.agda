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

module Examples.Groups.Clifford+CS.Four.Wins.W27 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn01332 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • CS) ≈ insʷ 0 (CS • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑))
wn01332 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn01333 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X • (S • CK₀₁) • X) ≈ insʷ 0 (X • (S • CK₀₁) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑))
wn01333 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X • (S • CK₀₁) • X) (X • (S • CK₀₁) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn01334 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X) ≈ insʷ 0 (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑))
wn01334 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X) (X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CS ↑) • X • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • (Swap ↑ • CK₀₁ • Swap ↑) • CX₀₁ • (CK₀₁ ↑) • (S ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (S ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • (CS ↑) • CX₀₁ • (CS ↑) • (CS ↑) • (CK₀₁ ↑) • (CS ↑) • (CK₀₁ ↑) • (CK₀₁ ↑)) _ _ Eq.refl
wn01335 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (X • S • X • S) ≈ insʷ 3 (iI)
wn01335 = win 3 0 complete₃ (X • S • X • S) (iI) _ _ Eq.refl
wn01336 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (Swap ↑ • CZ • Swap ↑) • K) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑))
wn01336 = win 3 0 complete₃ ((K • iI) • (Swap ↑ • CZ • Swap ↑) • K) ((Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn01337 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ) ≈ insʷ 0 (CCZ)
wn01337 = win 0 3 complete₃ (CCZ) (CCZ) _ _ Eq.refl
wn01338 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (Swap ↑ • CX₁₀ • Swap ↑) • (K • iI)) ≈ insʷ 3 ((Swap ↑ • CZ • Swap ↑))
wn01338 = win 3 0 complete₃ (K • (Swap ↑ • CX₁₀ • Swap ↑) • (K • iI)) ((Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn01339 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • K) ≈ insʷ 3 (ε)
wn01339 = win 3 0 complete₃ ((K • iI) • K) (ε) _ _ Eq.refl
wn01340 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • CS • CCZ)
wn01340 = win 0 3 complete₃ ((CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑)) ((Swap ↑ • CS • Swap ↑) • CS • CCZ) _ _ Eq.refl
wn01341 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) ≈ insʷ 0 (CCZ • (CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn01341 = win 0 3 complete₃ ((CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) (CCZ • (CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01342 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 (ε)
wn01342 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) _ _ Eq.refl
wn01343 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • Toff) ≈ insʷ 3 (Toff • CCZ • (CZ ↑))
wn01343 = win 3 0 complete₃ (CCZ • Toff) (Toff • CCZ • (CZ ↑)) _ _ Eq.refl
wn01344 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (CZ ↑) • Toff) ≈ insʷ 3 (Toff • CCZ)
wn01344 = win 3 0 complete₃ (CCZ • (CZ ↑) • Toff) (Toff • CCZ) _ _ Eq.refl
wn01345 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CZ ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (CZ ↑))
wn01345 = win 3 0 complete₃ ((CZ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CZ ↑)) _ _ Eq.refl
wn01346 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CZ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CZ ↑))
wn01346 = win 3 0 complete₃ ((CZ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CZ ↑)) _ _ Eq.refl
wn01347 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑) • CCZ • ((K • iI) ↑))
wn01347 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((K ↑) • CCZ • ((K • iI) ↑)) _ _ Eq.refl
wn01348 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K • iI) • (Swap ↑ • CZ • Swap ↑) • K) ≈ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑))
wn01348 = win 0 3 complete₃ ((K • iI) • (Swap ↑ • CZ • Swap ↑) • K) ((Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn01349 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (K • (Swap ↑ • CX₁₀ • Swap ↑) • (K • iI)) ≈ insʷ 0 ((Swap ↑ • CZ • Swap ↑))
wn01349 = win 0 3 complete₃ (K • (Swap ↑ • CX₁₀ • Swap ↑) • (K • iI)) ((Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn01350 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 (Swap • (Swap ↑) • Swap • Swap • (Swap ↑) • Swap)
wn01350 = win 0 3 complete₃ (ε) (Swap • (Swap ↑) • Swap • Swap • (Swap ↑) • Swap) _ _ Eq.refl
wn01351 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑))
wn01351 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01352 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn01352 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01353 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (S ↑ ↑))
wn01353 = win 3 0 complete₃ ((S ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (S ↑ ↑)) _ _ Eq.refl
wn01354 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((S • S • S) ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑ ↑))
wn01354 = win 3 0 complete₃ (((S • S • S) ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn01355 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn01355 = win 3 0 complete₃ (ε) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn01356 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ≈ insʷ 3 (ε)
wn01356 = win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (ε) _ _ Eq.refl
wn01357 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn01357 = win 3 0 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01358 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 (ε)
wn01358 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn01359 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ≈ insʷ 3 (CX₀₁ • (K ↑ • CCZ • K ↑ • iI))
wn01359 = win 3 0 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01360 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CX₀₁) ≈ insʷ 3 (CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn01360 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01361 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑))
wn01361 = win 3 0 complete₃ (CX₀₁ • (K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) _ _ Eq.refl
wn01362 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 3 (CX₁₀ • Toff)
wn01362 = win 3 0 complete₃ ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) _ _ Eq.refl
wn01363 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CX₁₀) ≈ insʷ 3 (CX₁₀ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ)
wn01363 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀) (CX₁₀ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) _ _ Eq.refl
wn01364 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CX₁₀ • Toff) ≈ insʷ 3 ((X ↑ ↑) • Toff • (X ↑ ↑))
wn01364 = win 3 0 complete₃ (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) _ _ Eq.refl
wn01365 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 0 (ε)
wn01365 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) _ _ Eq.refl
wn01366 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn01366 = win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01367 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn01367 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01368 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • S)
wn01368 = win 3 0 complete₃ (S • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • S) _ _ Eq.refl
wn01369 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn01369 = win 0 3 complete₃ (ε) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn01370 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ≈ insʷ 0 (ε)
wn01370 = win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (ε) _ _ Eq.refl
wn01371 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((CK₁₀ ↑) • ((S ↑ • CK₁₀) ↑))
wn01371 = win 0 3 complete₃ (ε) ((CK₁₀ ↑) • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn01372 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑)) ≈ insʷ 0 (ε)
wn01372 = win 0 3 complete₃ (((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑)) (ε) _ _ Eq.refl
wn01373 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 0 (CX₁₀ • Toff)
wn01373 = win 0 3 complete₃ ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) _ _ Eq.refl
wn01374 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • Toff) ≈ insʷ 0 (Toff • (CS ↑))
wn01374 = win 0 3 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) _ _ Eq.refl
wn01375 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CX₁₀ • Toff) ≈ insʷ 0 ((X ↑ ↑) • Toff • (X ↑ ↑))
wn01375 = win 0 3 complete₃ (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) _ _ Eq.refl
wn01376 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn01376 = win 0 3 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01377 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI))
wn01377 = win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01378 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn01378 = win 0 3 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn01379 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 (ε)
wn01379 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) _ _ Eq.refl
wn01380 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 (ε)
wn01380 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) _ _ Eq.refl
wn01381 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 (ε)
wn01381 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) _ _ Eq.refl
wn01382 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • CX₁₀) ≈ insʷ 3 (CX₁₀ • (CS ↑))
wn01382 = win 3 0 complete₃ ((CS ↑) • CX₁₀) (CX₁₀ • (CS ↑)) _ _ Eq.refl
wn01383 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • Toffᵗ) ≈ insʷ 3 (Toffᵗ • (S • S • S))
wn01383 = win 3 0 complete₃ ((S • S • S) • Toffᵗ) (Toffᵗ • (S • S • S)) _ _ Eq.refl
wn01384 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((S • S • S) ↑ ↑) • Toff) ≈ insʷ 3 (Toff • ((S • S • S) ↑ ↑))
wn01384 = win 3 0 complete₃ (((S • S • S) ↑ ↑) • Toff) (Toff • ((S • S • S) ↑ ↑)) _ _ Eq.refl
wn01385 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑ ↑) • Toff) ≈ insʷ 3 (Toff • (S ↑ ↑))
wn01385 = win 3 0 complete₃ ((S ↑ ↑) • Toff) (Toff • (S ↑ ↑)) _ _ Eq.refl
wn01386 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff) ≈ insʷ 3 ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑))
wn01386 = win 3 0 complete₃ (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01387 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 0 (ε)
wn01387 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) _ _ Eq.refl
wn01388 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • Toffᵗ) ≈ insʷ 3 (Toffᵗ • S)
wn01388 = win 3 0 complete₃ (S • Toffᵗ) (Toffᵗ • S) _ _ Eq.refl
wn01389 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 0 ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑))
wn01389 = win 0 3 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01390 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑))
wn01390 = win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) _ _ Eq.refl
wn01391 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑) • (X ↑ ↑))
wn01391 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01392 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑)) ≈ insʷ 0 ((K ↑ • CCZ • K ↑ • iI))
wn01392 = win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (X ↑ ↑)) ((K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn01393 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑))
wn01393 = win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) _ _ Eq.refl
wn01394 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (X ↑ ↑))
wn01394 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01395 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • Toff • (X ↑)) ≈ insʷ 0 ((X ↑) • CK₁₀ • (X ↑) • (Swap ↑ • CZ • Swap ↑) • (CS ↑) • CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑))
wn01395 = win 0 3 complete₃ ((X ↑) • Toff • (X ↑)) ((X ↑) • CK₁₀ • (X ↑) • (Swap ↑ • CZ • Swap ↑) • (CS ↑) • CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn01396 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • CK₁₀ • (X ↑) • (Swap ↑ • CZ • Swap ↑) • (CS ↑) • CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ≈ insʷ 0 ((X ↑) • Toff • (X ↑))
wn01396 = win 0 3 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (Swap ↑ • CZ • Swap ↑) • (CS ↑) • CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • Toff • (X ↑)) _ _ Eq.refl
wn01397 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Toffᵗ) ≈ insʷ 0 ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑))
wn01397 = win 0 3 complete₃ (Toffᵗ) ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑)) _ _ Eq.refl
wn01398 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑)) ≈ insʷ 0 (Toffᵗ)
wn01398 = win 0 3 complete₃ ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑)) (Toffᵗ) _ _ Eq.refl
wn01399 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀)
wn01399 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) _ _ Eq.refl
wn01400 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑))
wn01400 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₁₀ ↑) • CK₁₀ • (S ↑) • CK₁₀ • (S ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (X ↑ ↑)) _ _ Eq.refl
wn01401 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • CZ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑))
wn01401 = win 0 3 complete₃ ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • CZ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01402 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • CZ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑))
wn01402 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • CZ • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) _ _ Eq.refl
wn01403 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CK₁₀ • CS • CS)
wn01403 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CK₁₀ • CS • CS) _ _ Eq.refl
wn01404 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑))
wn01404 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (X ↑ ↑) • (CX₁₀ ↑) • (X ↑ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS • (X ↑ ↑)) _ _ Eq.refl
wn01405 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (X • Toffᵗ • X) ≈ insʷ 0 (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X)
wn01405 = win 0 3 complete₃ (X • Toffᵗ • X) (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) _ _ Eq.refl
wn01406 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) ≈ insʷ 0 (X • Toffᵗ • X)
wn01406 = win 0 3 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (CZ ↑) • CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • Toffᵗ • X) _ _ Eq.refl
wn01407 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn01407 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01408 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn01408 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01409 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CK₁₀ ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑))
wn01409 = win 0 3 complete₃ ((CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01410 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑))
wn01410 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑)) _ _ Eq.refl
wn01411 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ≈ insʷ 3 ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn01411 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01412 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ≈ insʷ 0 ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn01412 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01413 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn01413 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01414 : (₁₊ (1 +ℕ 2)) ⊢ insʷ 1 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X) ≈ insʷ 1 (X • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑))
wn01414 = win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01415 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑))
wn01415 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn01416 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) ≈ insʷ 3 (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn01416 = win 3 0 complete₃ (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn01417 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn01417 = win 3 0 complete₃ (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn01418 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S ↑) • Toff) ≈ insʷ 3 (Toff • (S ↑))
wn01418 = win 3 0 complete₃ ((S ↑) • Toff) (Toff • (S ↑)) _ _ Eq.refl
wn01419 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CX₁₀ • (X ↑) • X) ≈ insʷ 3 (X • (X ↑) • CX₁₀ • (X ↑))
wn01419 = win 3 0 complete₃ ((X ↑) • CX₁₀ • (X ↑) • X) (X • (X ↑) • CX₁₀ • (X ↑)) _ _ Eq.refl
wn01420 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS) ≈ insʷ 0 (CS • CS • CK₁₀ • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn01420 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CK₁₀ • CS) (CS • CS • CK₁₀ • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
