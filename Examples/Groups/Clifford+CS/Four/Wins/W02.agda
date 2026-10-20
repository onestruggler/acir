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

module Examples.Groups.Clifford+CS.Four.Wins.W02 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn00216 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • Swap) ≈ insʷ 3 (Swap • CS)
wn00216 = win 3 0 complete₃ (CS • Swap) (Swap • CS) _ _ Eq.refl
wn00217 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • Swap) ≈ insʷ 3 (Swap • X)
wn00217 = win 3 0 complete₃ ((X ↑) • Swap) (Swap • X) _ _ Eq.refl
wn00218 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CK₁₀ • Swap) ≈ insʷ 3 (Swap • CK₀₁)
wn00218 = win 3 0 complete₃ (CK₁₀ • Swap) (Swap • CK₀₁) _ _ Eq.refl
wn00219 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • CS) ≈ insʷ 3 (CS • Swap)
wn00219 = win 3 0 complete₃ (Swap • CS) (CS • Swap) _ _ Eq.refl
wn00220 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • X) ≈ insʷ 3 ((X ↑) • Swap)
wn00220 = win 3 0 complete₃ (Swap • X) ((X ↑) • Swap) _ _ Eq.refl
wn00221 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • CK₀₁) ≈ insʷ 3 (CK₁₀ • Swap)
wn00221 = win 3 0 complete₃ (Swap • CK₀₁) (CK₁₀ • Swap) _ _ Eq.refl
wn00222 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (X ↑)) ≈ insʷ 3 ((X ↑ ↑) • (Swap ↑))
wn00222 = win 3 0 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00223 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn00223 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00224 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • Toff • (K • iI)) ≈ insʷ 3 (CCZ)
wn00224 = win 3 0 complete₃ (K • Toff • (K • iI)) (CCZ) _ _ Eq.refl
wn00225 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((X ↑ ↑) • (X ↑ ↑))
wn00225 = win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00226 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (K • iI)) ≈ insʷ 3 ((K • iI) • Toff)
wn00226 = win 3 0 complete₃ (CCZ • (K • iI)) ((K • iI) • Toff) _ _ Eq.refl
wn00227 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff • Toff) ≈ insʷ 3 (ε)
wn00227 = win 3 0 complete₃ (Toff • Toff) (ε) _ _ Eq.refl
wn00228 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff • K) ≈ insʷ 3 (K • CCZ)
wn00228 = win 3 0 complete₃ (Toff • K) (K • CCZ) _ _ Eq.refl
wn00229 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (K • iI)) ≈ insʷ 3 ((K • iI) • (CS ↑))
wn00229 = win 3 0 complete₃ ((CS ↑) • (K • iI)) ((K • iI) • (CS ↑)) _ _ Eq.refl
wn00230 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • K) ≈ insʷ 3 (K • (CS ↑))
wn00230 = win 3 0 complete₃ ((CS ↑) • K) (K • (CS ↑)) _ _ Eq.refl
wn00231 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn00231 = win 3 0 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00232 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑))
wn00232 = win 3 0 complete₃ (ε) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00233 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑))
wn00233 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00234 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • CS) ≈ insʷ 0 (CS • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑))
wn00234 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00235 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ≈ insʷ 0 ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑))
wn00235 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00236 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • CCZ) ≈ insʷ 3 (CCZ • (S • S • S))
wn00236 = win 3 0 complete₃ ((S • S • S) • CCZ) (CCZ • (S • S • S)) _ _ Eq.refl
wn00237 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • CCZ) ≈ insʷ 3 (CCZ • S)
wn00237 = win 3 0 complete₃ (S • CCZ) (CCZ • S) _ _ Eq.refl
wn00238 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑))
wn00238 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00239 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑))
wn00239 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00240 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn00240 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00241 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑))
wn00241 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00242 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (S ↑)) ≈ insʷ 3 ((S ↑) • (Swap ↑ • CS • Swap ↑))
wn00242 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (S ↑)) ((S ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00243 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑)) ≈ insʷ 3 (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑))
wn00243 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00244 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00244 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00245 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CS) ≈ insʷ 3 (CS • (Swap ↑ • CS • Swap ↑))
wn00245 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00246 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑))
wn00246 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00247 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff)
wn00247 = win 3 0 complete₃ (Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00248 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑))
wn00248 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00249 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • CS) ≈ insʷ 0 (CS • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑))
wn00249 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00250 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ≈ insʷ 0 ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑))
wn00250 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00251 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CCZ)
wn00251 = win 3 0 complete₃ (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) _ _ Eq.refl
wn00252 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑))
wn00252 = win 3 0 complete₃ (ε) ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00253 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CX₀₁ ↑) • Swap) ≈ insʷ 3 (Swap • (Swap ↑ • CX₀₁ • Swap ↑))
wn00253 = win 3 0 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00254 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ)
wn00254 = win 3 0 complete₃ (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) _ _ Eq.refl
wn00255 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑))
wn00255 = win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00256 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑))
wn00256 = win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00257 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (X ↑))
wn00257 = win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) _ _ Eq.refl
wn00258 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑))
wn00258 = win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) _ _ Eq.refl
wn00259 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • CCZ)
wn00259 = win 0 3 complete₃ (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) _ _ Eq.refl
wn00260 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ)
wn00260 = win 0 3 complete₃ (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) _ _ Eq.refl
wn00261 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑))
wn00261 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00262 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn00262 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00263 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn00263 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00264 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) ≈ insʷ 3 (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00264 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00265 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • CS) ≈ insʷ 3 (CS • S)
wn00265 = win 3 0 complete₃ (S • CS) (CS • S) _ _ Eq.refl
wn00266 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ • (CS ↑)) ≈ insʷ 0 ((CS ↑) • CCZ)
wn00266 = win 0 3 complete₃ (CCZ • (CS ↑)) ((CS ↑) • CCZ) _ _ Eq.refl
wn00267 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ • (CZ ↑)) ≈ insʷ 0 ((CZ ↑) • CCZ)
wn00267 = win 0 3 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) _ _ Eq.refl
wn00268 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • S)
wn00268 = win 3 0 complete₃ (S • (CS • CS • CS)) ((CS • CS • CS) • S) _ _ Eq.refl
wn00269 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • CCZ)
wn00269 = win 0 3 complete₃ (CCZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00270 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00270 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00271 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑) • Swap) ≈ insʷ 3 (Swap • K)
wn00271 = win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) _ _ Eq.refl
wn00272 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) ≈ insʷ 3 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI)
wn00272 = win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00273 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CK₁₀ ↑) • Swap) ≈ insʷ 3 (Swap • (Swap ↑ • CK₁₀ • Swap ↑))
wn00273 = win 3 0 complete₃ ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00274 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ≈ insʷ 3 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI)
wn00274 = win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00275 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ≈ insʷ 3 ((CK₁₀ ↑) • Swap)
wn00275 = win 3 0 complete₃ (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) _ _ Eq.refl
wn00276 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑))
wn00276 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00277 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑))
wn00277 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00278 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑))
wn00278 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00279 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) ≈ insʷ 0 (Swap • (CK₁₀ ↑))
wn00279 = win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) _ _ Eq.refl
wn00280 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CK₁₀ ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑ • CK₁₀ • Swap ↑))
wn00280 = win 0 3 complete₃ ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00281 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑))
wn00281 = win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00282 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) ≈ insʷ 0 (Swap • ((S ↑ • CK₁₀) ↑))
wn00282 = win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn00283 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((S ↑ • CK₁₀) ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn00283 = win 0 3 complete₃ (((S ↑ • CK₁₀) ↑) • Swap) (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00284 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑))
wn00284 = win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00285 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑))
wn00285 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00286 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑))
wn00286 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00287 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑))
wn00287 = win 0 3 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00288 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑))
wn00288 = win 0 3 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00289 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff • (S ↑)) ≈ insʷ 3 ((S ↑) • Toff)
wn00289 = win 3 0 complete₃ (Toff • (S ↑)) ((S ↑) • Toff) _ _ Eq.refl
wn00290 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff • ((S • S • S) ↑)) ≈ insʷ 3 (((S • S • S) ↑) • Toff)
wn00290 = win 3 0 complete₃ (Toff • ((S • S • S) ↑)) (((S • S • S) ↑) • Toff) _ _ Eq.refl
wn00291 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑)) ≈ insʷ 3 ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00291 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑)) ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00292 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑)) ≈ insʷ 3 (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00292 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00293 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI))
wn00293 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00294 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • (CS ↑)) ≈ insʷ 3 ((CS ↑) • S)
wn00294 = win 3 0 complete₃ (S • (CS ↑)) ((CS ↑) • S) _ _ Eq.refl
wn00295 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • ((CS • CS • CS) ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • S)
wn00295 = win 3 0 complete₃ (S • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • S) _ _ Eq.refl
wn00296 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • Toff) ≈ insʷ 3 (Toff • (X ↑) • CS • (X ↑))
wn00296 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • Toff) (Toff • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00297 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑))
wn00297 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00298 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑))
wn00298 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00299 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑))
wn00299 = win 3 0 complete₃ ((CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00300 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑))
wn00300 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00301 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CZ • Swap ↑) • CCZ)
wn00301 = win 3 0 complete₃ (CCZ • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CCZ) _ _ Eq.refl
wn00302 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CZ • Swap ↑) • (CS ↑))
wn00302 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00303 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CZ • Swap ↑) • ((CS • CS • CS) ↑))
wn00303 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00304 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑))
wn00304 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00305 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI))
wn00305 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00306 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (S • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • S)
wn00306 = win 0 3 complete₃ (S • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • S) _ _ Eq.refl
wn00307 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S)
wn00307 = win 0 3 complete₃ (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S) _ _ Eq.refl
wn00308 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (S • S • S))
wn00308 = win 0 3 complete₃ ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00309 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S))
wn00309 = win 0 3 complete₃ ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00310 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00310 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00311 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • S) ≈ insʷ 3 ((S ↑) • Swap)
wn00311 = win 3 0 complete₃ (Swap • S) ((S ↑) • Swap) _ _ Eq.refl
wn00312 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (S • S • S)) ≈ insʷ 3 (((S • S • S) ↑) • Swap)
wn00312 = win 3 0 complete₃ (Swap • (S • S • S)) (((S • S • S) ↑) • Swap) _ _ Eq.refl
wn00313 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (K • iI)) ≈ insʷ 3 (((K • iI) ↑) • Swap)
wn00313 = win 3 0 complete₃ (Swap • (K • iI)) (((K • iI) ↑) • Swap) _ _ Eq.refl
wn00314 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • Z) ≈ insʷ 3 ((Z ↑) • Swap)
wn00314 = win 3 0 complete₃ (Swap • Z) ((Z ↑) • Swap) _ _ Eq.refl
wn00315 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (S ↑)) ≈ insʷ 3 (S • Swap)
wn00315 = win 3 0 complete₃ (Swap • (S ↑)) (S • Swap) _ _ Eq.refl
wn00316 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • ((S • S • S) ↑)) ≈ insʷ 3 ((S • S • S) • Swap)
wn00316 = win 3 0 complete₃ (Swap • ((S • S • S) ↑)) ((S • S • S) • Swap) _ _ Eq.refl
wn00317 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (X ↑)) ≈ insʷ 3 (X • Swap)
wn00317 = win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) _ _ Eq.refl
wn00318 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Z ↑)) ≈ insʷ 3 (Z • Swap)
wn00318 = win 3 0 complete₃ (Swap • (Z ↑)) (Z • Swap) _ _ Eq.refl
wn00319 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (CS • CS • CS)) ≈ insʷ 3 ((CS • CS • CS) • Swap)
wn00319 = win 3 0 complete₃ (Swap • (CS • CS • CS)) ((CS • CS • CS) • Swap) _ _ Eq.refl
wn00320 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • CZ) ≈ insʷ 3 (CZ • Swap)
wn00320 = win 3 0 complete₃ (Swap • CZ) (CZ • Swap) _ _ Eq.refl
wn00321 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (S • CK₀₁)) ≈ insʷ 3 ((S ↑ • CK₁₀) • Swap)
wn00321 = win 3 0 complete₃ (Swap • (S • CK₀₁)) ((S ↑ • CK₁₀) • Swap) _ _ Eq.refl
wn00322 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • Swap)
wn00322 = win 3 0 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) _ _ Eq.refl
wn00323 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 3 ((CZ ↑) • Swap)
wn00323 = win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) _ _ Eq.refl
wn00324 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ≈ insʷ 3 ((CK₀₁ ↑) • Swap)
wn00324 = win 3 0 complete₃ (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) _ _ Eq.refl
wn00325 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) ≈ insʷ 3 (((S • CK₀₁) ↑) • Swap)
wn00325 = win 3 0 complete₃ (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) _ _ Eq.refl
wn00326 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • CX₁₀) ≈ insʷ 3 (CX₀₁ • Swap)
wn00326 = win 3 0 complete₃ (Swap • CX₁₀) (CX₀₁ • Swap) _ _ Eq.refl
wn00327 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • CK₁₀) ≈ insʷ 3 (CK₀₁ • Swap)
wn00327 = win 3 0 complete₃ (Swap • CK₁₀) (CK₀₁ • Swap) _ _ Eq.refl
wn00328 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (S ↑ • CK₁₀)) ≈ insʷ 3 ((S • CK₀₁) • Swap)
wn00328 = win 3 0 complete₃ (Swap • (S ↑ • CK₁₀)) ((S • CK₀₁) • Swap) _ _ Eq.refl
wn00329 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (CK₀₁ ↑)) ≈ insʷ 3 ((Swap ↑ • CK₀₁ • Swap ↑) • Swap)
wn00329 = win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00330 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • ((S • CK₀₁) ↑)) ≈ insʷ 3 ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap)
wn00330 = win 3 0 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) _ _ Eq.refl
wn00331 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 3 ((CX₁₀ ↑) • Swap)
wn00331 = win 3 0 complete₃ (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) _ _ Eq.refl
wn00332 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ≈ insʷ 3 (((S ↑ • CK₁₀) ↑) • Swap)
wn00332 = win 3 0 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) _ _ Eq.refl
wn00333 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ≈ insʷ 3 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI)
wn00333 = win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00334 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ≈ insʷ 0 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI)
wn00334 = win 0 3 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00335 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (K ↑)) ≈ insʷ 0 ((K ↑ ↑) • (Swap ↑))
wn00335 = win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00336 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (K ↑ ↑)) ≈ insʷ 0 ((K ↑) • (Swap ↑))
wn00336 = win 0 3 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) _ _ Eq.refl
wn00337 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ≈ insʷ 0 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI)
wn00337 = win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00338 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (S ↑)) ≈ insʷ 3 ((S ↑ ↑) • (Swap ↑))
wn00338 = win 3 0 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00339 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • ((S • S • S) ↑)) ≈ insʷ 3 (((S • S • S) ↑ ↑) • (Swap ↑))
wn00339 = win 3 0 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00340 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (K ↑)) ≈ insʷ 3 ((K ↑ ↑) • (Swap ↑))
wn00340 = win 3 0 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00341 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • ((K • iI) ↑)) ≈ insʷ 3 (((K • iI) ↑ ↑) • (Swap ↑))
wn00341 = win 3 0 complete₃ ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00342 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (Z ↑)) ≈ insʷ 3 ((Z ↑ ↑) • (Swap ↑))
wn00342 = win 3 0 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00343 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (S ↑ ↑)) ≈ insʷ 3 ((S ↑) • (Swap ↑))
wn00343 = win 3 0 complete₃ ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) _ _ Eq.refl
wn00344 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • ((S • S • S) ↑ ↑)) ≈ insʷ 3 (((S • S • S) ↑) • (Swap ↑))
wn00344 = win 3 0 complete₃ ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) _ _ Eq.refl
wn00345 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (K ↑ ↑)) ≈ insʷ 3 ((K ↑) • (Swap ↑))
wn00345 = win 3 0 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) _ _ Eq.refl
wn00346 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • ((K • iI) ↑ ↑)) ≈ insʷ 3 (((K • iI) ↑) • (Swap ↑))
wn00346 = win 3 0 complete₃ ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) _ _ Eq.refl
wn00347 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑) • (Swap ↑))
wn00347 = win 3 0 complete₃ ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) _ _ Eq.refl
wn00348 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (Z ↑ ↑)) ≈ insʷ 3 ((Z ↑) • (Swap ↑))
wn00348 = win 3 0 complete₃ ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) _ _ Eq.refl
wn00349 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CZ ↑)) ≈ insʷ 3 ((CZ ↑) • (Swap ↑))
wn00349 = win 3 0 complete₃ ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) _ _ Eq.refl
wn00350 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CK₀₁ ↑)) ≈ insʷ 3 ((CK₁₀ ↑) • (Swap ↑))
wn00350 = win 3 0 complete₃ ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00351 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • ((S • CK₀₁) ↑)) ≈ insʷ 3 (((S ↑ • CK₁₀) ↑) • (Swap ↑))
wn00351 = win 3 0 complete₃ ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) _ _ Eq.refl
wn00352 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ≈ insʷ 0 ((CK₀₁ ↑) • Swap)
wn00352 = win 0 3 complete₃ (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) _ _ Eq.refl
wn00353 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) ≈ insʷ 0 (((S • CK₀₁) ↑) • Swap)
wn00353 = win 0 3 complete₃ (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) _ _ Eq.refl
wn00354 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CX₁₀ ↑)) ≈ insʷ 3 ((CX₀₁ ↑) • (Swap ↑))
wn00354 = win 3 0 complete₃ ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00355 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CK₁₀ ↑)) ≈ insʷ 3 ((CK₀₁ ↑) • (Swap ↑))
wn00355 = win 3 0 complete₃ ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00356 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) ≈ insʷ 3 (((S • CK₀₁) ↑) • (Swap ↑))
wn00356 = win 3 0 complete₃ ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) _ _ Eq.refl
wn00357 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (CK₀₁ ↑)) ≈ insʷ 0 ((Swap ↑ • CK₀₁ • Swap ↑) • Swap)
wn00357 = win 0 3 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00358 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • ((S • CK₀₁) ↑)) ≈ insʷ 0 ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap)
wn00358 = win 0 3 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) _ _ Eq.refl
wn00359 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ≈ insʷ 0 ((CK₁₀ ↑) • Swap)
wn00359 = win 0 3 complete₃ (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) _ _ Eq.refl
wn00360 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) ≈ insʷ 0 (((S ↑ • CK₁₀) ↑) • Swap)
wn00360 = win 0 3 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) _ _ Eq.refl
wn00361 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (CK₁₀ ↑)) ≈ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑) • Swap)
wn00361 = win 0 3 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00362 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • ((S ↑ • CK₁₀) ↑)) ≈ insʷ 0 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap)
wn00362 = win 0 3 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) _ _ Eq.refl
wn00363 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ≈ insʷ 3 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI)
wn00363 = win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00364 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (iI ↑)) ≈ insʷ 3 ((iI ↑ ↑) • (Swap ↑))
wn00364 = win 3 0 complete₃ ((Swap ↑) • (iI ↑)) ((iI ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00365 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ≈ insʷ 0 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI)
wn00365 = win 0 3 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00366 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ≈ insʷ 3 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI)
wn00366 = win 3 0 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00367 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) ≈ insʷ 0 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI)
wn00367 = win 0 3 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00368 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ≈ insʷ 3 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI)
wn00368 = win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00369 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ≈ insʷ 0 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI)
wn00369 = win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00370 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • ((K • iI) ↑)) ≈ insʷ 0 (((K • iI) ↑ ↑) • (Swap ↑))
wn00370 = win 0 3 complete₃ ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00371 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (Z ↑)) ≈ insʷ 0 ((Z ↑ ↑) • (Swap ↑))
wn00371 = win 0 3 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00372 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (S ↑ ↑)) ≈ insʷ 0 ((S ↑) • (Swap ↑))
wn00372 = win 0 3 complete₃ ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) _ _ Eq.refl
wn00373 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • ((S • S • S) ↑ ↑)) ≈ insʷ 0 (((S • S • S) ↑) • (Swap ↑))
wn00373 = win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) _ _ Eq.refl
wn00374 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • ((K • iI) ↑ ↑)) ≈ insʷ 0 (((K • iI) ↑) • (Swap ↑))
wn00374 = win 0 3 complete₃ ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) _ _ Eq.refl
wn00375 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (X ↑ ↑)) ≈ insʷ 0 ((X ↑) • (Swap ↑))
wn00375 = win 0 3 complete₃ ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) _ _ Eq.refl
wn00376 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (Z ↑ ↑)) ≈ insʷ 0 ((Z ↑) • (Swap ↑))
wn00376 = win 0 3 complete₃ ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) _ _ Eq.refl
wn00377 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (CZ ↑)) ≈ insʷ 0 ((CZ ↑) • (Swap ↑))
wn00377 = win 0 3 complete₃ ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) _ _ Eq.refl
wn00378 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (CX₀₁ ↑)) ≈ insʷ 0 ((CX₁₀ ↑) • (Swap ↑))
wn00378 = win 0 3 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00379 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (CK₀₁ ↑)) ≈ insʷ 0 ((CK₁₀ ↑) • (Swap ↑))
wn00379 = win 0 3 complete₃ ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00380 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • ((S • CK₀₁) ↑)) ≈ insʷ 0 (((S ↑ • CK₁₀) ↑) • (Swap ↑))
wn00380 = win 0 3 complete₃ ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) _ _ Eq.refl
wn00381 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (CX₁₀ ↑)) ≈ insʷ 0 ((CX₀₁ ↑) • (Swap ↑))
wn00381 = win 0 3 complete₃ ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00382 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (CK₁₀ ↑)) ≈ insʷ 0 ((CK₀₁ ↑) • (Swap ↑))
wn00382 = win 0 3 complete₃ ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00383 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) ≈ insʷ 0 (((S • CK₀₁) ↑) • (Swap ↑))
wn00383 = win 0 3 complete₃ ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) _ _ Eq.refl
wn00384 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) ≈ insʷ 0 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI)
wn00384 = win 0 3 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00385 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ≈ insʷ 0 ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI)
wn00385 = win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00386 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ≈ insʷ 0 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI)
wn00386 = win 0 3 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00387 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (X • X) ≈ insʷ 3 (ε)
wn00387 = win 3 0 complete₃ (X • X) (ε) _ _ Eq.refl
wn00388 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑) • (X ↑)) ≈ insʷ 3 (ε)
wn00388 = win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) _ _ Eq.refl
wn00389 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (X ↑ ↑)) ≈ insʷ 3 (ε)
wn00389 = win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn00390 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (X ↑ ↑)) ≈ insʷ 0 (ε)
wn00390 = win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn00391 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (X • S • K) ≈ insʷ 3 ((S • S • S) • (K • iI) • S • S)
wn00391 = win 3 0 complete₃ (X • S • K) ((S • S • S) • (K • iI) • S • S) _ _ Eq.refl
wn00392 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S • S • S) • X) ≈ insʷ 3 ((S • S • S) • (S • S • S) • K • S)
wn00392 = win 3 0 complete₃ ((K • iI) • (S • S • S) • X) ((S • S • S) • (S • S • S) • K • S) _ _ Eq.refl
wn00393 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (S ↑ ↑) • (K ↑ ↑)) ≈ insʷ 3 (((S • S • S) ↑ ↑) • ((K • iI) ↑ ↑) • (S ↑ ↑) • (S ↑ ↑))
wn00393 = win 3 0 complete₃ ((X ↑ ↑) • (S ↑ ↑) • (K ↑ ↑)) (((S • S • S) ↑ ↑) • ((K • iI) ↑ ↑) • (S ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00394 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((K • iI) ↑ ↑) • ((S • S • S) ↑ ↑) • (X ↑ ↑)) ≈ insʷ 3 (((S • S • S) ↑ ↑) • ((S • S • S) ↑ ↑) • (K ↑ ↑) • (S ↑ ↑))
wn00394 = win 3 0 complete₃ (((K • iI) ↑ ↑) • ((S • S • S) ↑ ↑) • (X ↑ ↑)) (((S • S • S) ↑ ↑) • ((S • S • S) ↑ ↑) • (K ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00395 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 0 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑))
wn00395 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00396 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • CS) ≈ insʷ 0 (CS • (X ↑ ↑) • (CS ↑) • (X ↑ ↑))
wn00396 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00397 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (CS • CS • CS)) ≈ insʷ 0 ((CS • CS • CS) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑))
wn00397 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00398 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (K ↑))
wn00398 = win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) _ _ Eq.refl
wn00399 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑))
wn00399 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00400 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ≈ insʷ 0 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑))
wn00400 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00401 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • CS) ≈ insʷ 0 (CS • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑))
wn00401 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00402 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (CS • CS • CS)) ≈ insʷ 0 ((CS • CS • CS) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑))
wn00402 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00403 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) ≈ insʷ 0 (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑))
wn00403 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00404 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) ≈ insʷ 0 (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑))
wn00404 = win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00405 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) ≈ insʷ 0 (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑))
wn00405 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00406 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • (CS ↑)) ≈ insʷ 0 ((CS ↑) • CS)
wn00406 = win 0 3 complete₃ (CS • (CS ↑)) ((CS ↑) • CS) _ _ Eq.refl
wn00407 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CX₁₀ • (CS ↑)) ≈ insʷ 0 ((CS ↑) • CX₁₀)
wn00407 = win 0 3 complete₃ (CX₁₀ • (CS ↑)) ((CS ↑) • CX₁₀) _ _ Eq.refl
wn00408 : (₁₊ (1 +ℕ 2)) ⊢ insʷ 1 ((CS ↑) • S) ≈ insʷ 1 (S • (CS ↑))
wn00408 = win 1 2 complete₃ ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
