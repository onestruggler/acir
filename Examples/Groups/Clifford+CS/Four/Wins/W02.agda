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

module Examples.Groups.Clifford+CS.Four.Wins.W02 where

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

wn00216 : Base 3 → ⟪ (CS01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS01 ∷ []) ⟫ʷ
wn00216 b = win 3 0 b (CS • Swap) (Swap • CS) _ _ Eq.refl
wn00217 : Base 3 → ⟪ (X1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ X0 ∷ []) ⟫ʷ
wn00217 b = win 3 0 b ((X ↑) • Swap) (Swap • X) _ _ Eq.refl
wn00218 : Base 3 → ⟪ (CK10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK01 ∷ []) ⟫ʷ
wn00218 b = win 3 0 b (CK₁₀ • Swap) (Swap • CK₀₁) _ _ Eq.refl
wn00219 : Base 3 → ⟪ (Sw01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sw01 ∷ []) ⟫ʷ
wn00219 b = win 3 0 b (Swap • CS) (CS • Swap) _ _ Eq.refl
wn00220 : Base 3 → ⟪ (Sw01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw01 ∷ []) ⟫ʷ
wn00220 b = win 3 0 b (Swap • X) ((X ↑) • Swap) _ _ Eq.refl
wn00221 : Base 3 → ⟪ (Sw01 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ Sw01 ∷ []) ⟫ʷ
wn00221 b = win 3 0 b (Swap • CK₀₁) (CK₁₀ • Swap) _ _ Eq.refl
wn00222 : Base 3 → ⟪ (Sw12 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw12 ∷ []) ⟫ʷ
wn00222 b = win 3 0 b ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00223 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn00223 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00224 : Base 3 → ⟪ (K0 ∷ Toff012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00224 b = win 3 0 b (K • Toff • (K • iI)) (CCZ) _ _ Eq.refl
wn00225 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ
wn00225 b = win 0 3 b (ε) ((X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00226 : Base 3 → ⟪ (CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ []) ⟫ʷ
wn00226 b = win 3 0 b (CCZ • (K • iI)) ((K • iI) • Toff) _ _ Eq.refl
wn00227 : Base 3 → ⟪ (Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00227 b = win 3 0 b (Toff • Toff) (ε) _ _ Eq.refl
wn00228 : Base 3 → ⟪ (Toff012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CCZ012 ∷ []) ⟫ʷ
wn00228 b = win 3 0 b (Toff • K) (K • CCZ) _ _ Eq.refl
wn00229 : Base 3 → ⟪ (CS12 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00229 b = win 3 0 b ((CS ↑) • (K • iI)) ((K • iI) • (CS ↑)) _ _ Eq.refl
wn00230 : Base 3 → ⟪ (CS12 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ []) ⟫ʷ
wn00230 b = win 3 0 b ((CS ↑) • K) (K • (CS ↑)) _ _ Eq.refl
wn00231 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00231 b = win 3 0 b (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00232 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ
wn00232 b = win 3 0 b (ε) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00233 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn00233 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00234 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00234 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00235 : Base 3 → ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00235 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00236 : Base 3 → ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ
wn00236 b = win 3 0 b ((S • S • S) • CCZ) (CCZ • (S • S • S)) _ _ Eq.refl
wn00237 : Base 3 → ⟪ (S0 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ S0 ∷ []) ⟫ʷ
wn00237 b = win 3 0 b (S • CCZ) (CCZ • S) _ _ Eq.refl
wn00238 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn00238 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00239 : Base 3 → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn00239 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00240 : Base 3 → ⟪ (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn00240 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00241 : Base 3 → ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn00241 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00242 : Base 3 → ⟪ (CS02 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS02 ∷ []) ⟫ʷ
wn00242 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (S ↑)) ((S ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00243 : Base 3 → ⟪ (CS02 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00243 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00244 : Base 3 → ⟪ (CS02 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00244 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00245 : Base 3 → ⟪ (CS02 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02 ∷ []) ⟫ʷ
wn00245 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00246 : Base 3 → ⟪ (CS02 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00246 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00247 : Base 3 → ⟪ (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00247 b = win 3 0 b (Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00248 : Base 3 → ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn00248 b = win 3 0 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00249 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00249 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00250 : Base 3 → ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00250 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00251 : Base 3 → ⟪ (CCZ012 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
wn00251 b = win 3 0 b (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) _ _ Eq.refl
wn00252 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX02 ∷ CX02 ∷ []) ⟫ʷ
wn00252 b = win 3 0 b (ε) ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00253 : Base 3 → ⟪ (CX12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX02 ∷ []) ⟫ʷ
wn00253 b = win 3 0 b ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00254 : Base 3 → ⟪ (CCZ012 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00254 b = win 3 0 b (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) _ _ Eq.refl
wn00255 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00255 b = win 0 3 b ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00256 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00256 b = win 0 3 b ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00257 : Base 3 → ⟪ (X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ []) ⟫ʷ
wn00257 b = win 0 3 b ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) _ _ Eq.refl
wn00258 : Base 3 → ⟪ (X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ []) ⟫ʷ
wn00258 b = win 0 3 b ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) _ _ Eq.refl
wn00259 : Base 3 → ⟪ (CCZ123 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ123 ∷ []) ⟫ʷ
wn00259 b = win 0 3 b (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) _ _ Eq.refl
wn00260 : Base 3 → ⟪ (CCZ123 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn00260 b = win 0 3 b (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) _ _ Eq.refl
wn00261 : Base 3 → ⟪ (CX20 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CX20 ∷ []) ⟫ʷ
wn00261 b = win 3 0 b ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00262 : Base 3 → ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00262 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00263 : Base 3 → ⟪ (CS02 ∷ S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00263 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00264 : Base 3 → ⟪ (CS02⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00264 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00265 : Base 3 → ⟪ (S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ S0 ∷ []) ⟫ʷ
wn00265 b = win 3 0 b (S • CS) (CS • S) _ _ Eq.refl
wn00266 : Base 3 → ⟪ (CCZ123 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ123 ∷ []) ⟫ʷ
wn00266 b = win 0 3 b (CCZ • (CS ↑)) ((CS ↑) • CCZ) _ _ Eq.refl
wn00267 : Base 3 → ⟪ (CCZ123 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ123 ∷ []) ⟫ʷ
wn00267 b = win 0 3 b (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) _ _ Eq.refl
wn00268 : Base 3 → ⟪ (S0 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S0 ∷ []) ⟫ʷ
wn00268 b = win 3 0 b (S • (CS • CS • CS)) ((CS • CS • CS) • S) _ _ Eq.refl
wn00269 : Base 3 → ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn00269 b = win 0 3 b (CCZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00270 : Base 3 → ⟪ (CS02⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn00270 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00271 : Base 3 → ⟪ (K1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K0 ∷ []) ⟫ʷ
wn00271 b = win 3 0 b ((K ↑) • Swap) (Swap • K) _ _ Eq.refl
wn00272 : Base 3 → ⟪ (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00272 b = win 3 0 b (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00273 : Base 3 → ⟪ (CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK20 ∷ []) ⟫ʷ
wn00273 b = win 3 0 b ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00274 : Base 3 → ⟪ (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00274 b = win 3 0 b ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00275 : Base 3 → ⟪ (Sw01 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ Sw01 ∷ []) ⟫ʷ
wn00275 b = win 3 0 b (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) _ _ Eq.refl
wn00276 : Base 3 → ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn00276 b = win 0 3 b ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00277 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00277 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00278 : Base 3 → ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00278 b = win 3 0 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00279 : Base 3 → ⟪ (CK31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK32 ∷ []) ⟫ʷ
wn00279 b = win 0 3 b ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) _ _ Eq.refl
wn00280 : Base 3 → ⟪ (CK32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK31 ∷ []) ⟫ʷ
wn00280 b = win 0 3 b ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00281 : Base 3 → ⟪ (X2 ∷ CK21 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn00281 b = win 3 0 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00282 : Base 3 → ⟪ (CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK32⁻ ∷ []) ⟫ʷ
wn00282 b = win 0 3 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn00283 : Base 3 → ⟪ (CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK31⁻ ∷ []) ⟫ʷ
wn00283 b = win 0 3 b (((S ↑ • CK₁₀) ↑) • Swap) (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00284 : Base 3 → ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn00284 b = win 3 0 b ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00285 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00285 b = win 3 0 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00286 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00286 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00287 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00287 b = win 0 3 b ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00288 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00288 b = win 0 3 b ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00289 : Base 3 → ⟪ (Toff012 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Toff012 ∷ []) ⟫ʷ
wn00289 b = win 3 0 b (Toff • (S ↑)) ((S ↑) • Toff) _ _ Eq.refl
wn00290 : Base 3 → ⟪ (Toff012 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Toff012 ∷ []) ⟫ʷ
wn00290 b = win 3 0 b (Toff • ((S • S • S) ↑)) (((S • S • S) ↑) • Toff) _ _ Eq.refl
wn00291 : Base 3 → ⟪ (CS02⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00291 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑)) ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00292 : Base 3 → ⟪ (CS02⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn00292 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00293 : Base 3 → ⟪ (Toff102 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff102 ∷ []) ⟫ʷ
wn00293 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00294 : Base 3 → ⟪ (S0 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ S0 ∷ []) ⟫ʷ
wn00294 b = win 3 0 b (S • (CS ↑)) ((CS ↑) • S) _ _ Eq.refl
wn00295 : Base 3 → ⟪ (S0 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ S0 ∷ []) ⟫ʷ
wn00295 b = win 3 0 b (S • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • S) _ _ Eq.refl
wn00296 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00296 b = win 3 0 b ((X ↑) • CS • (X ↑) • Toff) (Toff • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00297 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00297 b = win 3 0 b ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00298 : Base 3 → ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00298 b = win 3 0 b ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00299 : Base 3 → ⟪ (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn00299 b = win 3 0 b ((CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00300 : Base 3 → ⟪ (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00300 b = win 3 0 b (((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00301 : Base 3 → ⟪ (CCZ012 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ012 ∷ []) ⟫ʷ
wn00301 b = win 3 0 b (CCZ • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CCZ) _ _ Eq.refl
wn00302 : Base 3 → ⟪ (CS12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12 ∷ []) ⟫ʷ
wn00302 b = win 3 0 b ((CS ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00303 : Base 3 → ⟪ (CS12⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00303 b = win 3 0 b (((CS • CS • CS) ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00304 : Base 3 → ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00304 b = win 3 0 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00305 : Base 3 → ⟪ (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00305 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00306 : Base 3 → ⟪ (S1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1 ∷ []) ⟫ʷ
wn00306 b = win 0 3 b (S • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • S) _ _ Eq.refl
wn00307 : Base 3 → ⟪ (S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1 ∷ []) ⟫ʷ
wn00307 b = win 0 3 b (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S) _ _ Eq.refl
wn00308 : Base 3 → ⟪ (S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1⁻ ∷ []) ⟫ʷ
wn00308 b = win 0 3 b ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00309 : Base 3 → ⟪ (S1⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
wn00309 b = win 0 3 b ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00310 : Base 3 → ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn00310 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00311 : Base 3 → ⟪ (Sw01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Sw01 ∷ []) ⟫ʷ
wn00311 b = win 3 0 b (Swap • S) ((S ↑) • Swap) _ _ Eq.refl
wn00312 : Base 3 → ⟪ (Sw01 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00312 b = win 3 0 b (Swap • (S • S • S)) (((S • S • S) ↑) • Swap) _ _ Eq.refl
wn00313 : Base 3 → ⟪ (Sw01 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00313 b = win 3 0 b (Swap • (K • iI)) (((K • iI) ↑) • Swap) _ _ Eq.refl
wn00314 : Base 3 → ⟪ (Sw01 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Sw01 ∷ []) ⟫ʷ
wn00314 b = win 3 0 b (Swap • Z) ((Z ↑) • Swap) _ _ Eq.refl
wn00315 : Base 3 → ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ
wn00315 b = win 3 0 b (Swap • (S ↑)) (S • Swap) _ _ Eq.refl
wn00316 : Base 3 → ⟪ (Sw01 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00316 b = win 3 0 b (Swap • ((S • S • S) ↑)) ((S • S • S) • Swap) _ _ Eq.refl
wn00317 : Base 3 → ⟪ (Sw01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sw01 ∷ []) ⟫ʷ
wn00317 b = win 3 0 b (Swap • (X ↑)) (X • Swap) _ _ Eq.refl
wn00318 : Base 3 → ⟪ (Sw01 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ Sw01 ∷ []) ⟫ʷ
wn00318 b = win 3 0 b (Swap • (Z ↑)) (Z • Swap) _ _ Eq.refl
wn00319 : Base 3 → ⟪ (Sw01 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00319 b = win 3 0 b (Swap • (CS • CS • CS)) ((CS • CS • CS) • Swap) _ _ Eq.refl
wn00320 : Base 3 → ⟪ (Sw01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw01 ∷ []) ⟫ʷ
wn00320 b = win 3 0 b (Swap • CZ) (CZ • Swap) _ _ Eq.refl
wn00321 : Base 3 → ⟪ (Sw01 ∷ CK01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00321 b = win 3 0 b (Swap • (S • CK₀₁)) ((S ↑ • CK₁₀) • Swap) _ _ Eq.refl
wn00322 : Base 3 → ⟪ (Sw01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00322 b = win 3 0 b (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) _ _ Eq.refl
wn00323 : Base 3 → ⟪ (Sw01 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw01 ∷ []) ⟫ʷ
wn00323 b = win 3 0 b (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) _ _ Eq.refl
wn00324 : Base 3 → ⟪ (Sw01 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ Sw01 ∷ []) ⟫ʷ
wn00324 b = win 3 0 b (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) _ _ Eq.refl
wn00325 : Base 3 → ⟪ (Sw01 ∷ CK02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00325 b = win 3 0 b (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) _ _ Eq.refl
wn00326 : Base 3 → ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ
wn00326 b = win 3 0 b (Swap • CX₁₀) (CX₀₁ • Swap) _ _ Eq.refl
wn00327 : Base 3 → ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ
wn00327 b = win 3 0 b (Swap • CK₁₀) (CK₀₁ • Swap) _ _ Eq.refl
wn00328 : Base 3 → ⟪ (Sw01 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00328 b = win 3 0 b (Swap • (S ↑ • CK₁₀)) ((S • CK₀₁) • Swap) _ _ Eq.refl
wn00329 : Base 3 → ⟪ (Sw01 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ Sw01 ∷ []) ⟫ʷ
wn00329 b = win 3 0 b (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00330 : Base 3 → ⟪ (Sw01 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00330 b = win 3 0 b (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) _ _ Eq.refl
wn00331 : Base 3 → ⟪ (Sw01 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Sw01 ∷ []) ⟫ʷ
wn00331 b = win 3 0 b (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) _ _ Eq.refl
wn00332 : Base 3 → ⟪ (Sw01 ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00332 b = win 3 0 b (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) _ _ Eq.refl
wn00333 : Base 3 → ⟪ (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00333 b = win 3 0 b ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00334 : Base 3 → ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00334 b = win 0 3 b ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00335 : Base 3 → ⟪ (Sw23 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sw23 ∷ []) ⟫ʷ
wn00335 b = win 0 3 b ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00336 : Base 3 → ⟪ (Sw23 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sw23 ∷ []) ⟫ʷ
wn00336 b = win 0 3 b ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) _ _ Eq.refl
wn00337 : Base 3 → ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00337 b = win 0 3 b ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00338 : Base 3 → ⟪ (Sw12 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Sw12 ∷ []) ⟫ʷ
wn00338 b = win 3 0 b ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00339 : Base 3 → ⟪ (Sw12 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00339 b = win 3 0 b ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00340 : Base 3 → ⟪ (Sw12 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sw12 ∷ []) ⟫ʷ
wn00340 b = win 3 0 b ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00341 : Base 3 → ⟪ (Sw12 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00341 b = win 3 0 b ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00342 : Base 3 → ⟪ (Sw12 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Sw12 ∷ []) ⟫ʷ
wn00342 b = win 3 0 b ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00343 : Base 3 → ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ
wn00343 b = win 3 0 b ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) _ _ Eq.refl
wn00344 : Base 3 → ⟪ (Sw12 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00344 b = win 3 0 b ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) _ _ Eq.refl
wn00345 : Base 3 → ⟪ (Sw12 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sw12 ∷ []) ⟫ʷ
wn00345 b = win 3 0 b ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) _ _ Eq.refl
wn00346 : Base 3 → ⟪ (Sw12 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00346 b = win 3 0 b ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) _ _ Eq.refl
wn00347 : Base 3 → ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ
wn00347 b = win 3 0 b ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) _ _ Eq.refl
wn00348 : Base 3 → ⟪ (Sw12 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Sw12 ∷ []) ⟫ʷ
wn00348 b = win 3 0 b ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) _ _ Eq.refl
wn00349 : Base 3 → ⟪ (Sw12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw12 ∷ []) ⟫ʷ
wn00349 b = win 3 0 b ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) _ _ Eq.refl
wn00350 : Base 3 → ⟪ (Sw12 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ Sw12 ∷ []) ⟫ʷ
wn00350 b = win 3 0 b ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00351 : Base 3 → ⟪ (Sw12 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00351 b = win 3 0 b ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) _ _ Eq.refl
wn00352 : Base 3 → ⟪ (Sw12 ∷ CK13 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ Sw12 ∷ []) ⟫ʷ
wn00352 b = win 0 3 b (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) _ _ Eq.refl
wn00353 : Base 3 → ⟪ (Sw12 ∷ CK13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00353 b = win 0 3 b (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) _ _ Eq.refl
wn00354 : Base 3 → ⟪ (Sw12 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Sw12 ∷ []) ⟫ʷ
wn00354 b = win 3 0 b ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00355 : Base 3 → ⟪ (Sw12 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ Sw12 ∷ []) ⟫ʷ
wn00355 b = win 3 0 b ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00356 : Base 3 → ⟪ (Sw12 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00356 b = win 3 0 b ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) _ _ Eq.refl
wn00357 : Base 3 → ⟪ (Sw12 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ Sw12 ∷ []) ⟫ʷ
wn00357 b = win 0 3 b (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00358 : Base 3 → ⟪ (Sw12 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00358 b = win 0 3 b (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) _ _ Eq.refl
wn00359 : Base 3 → ⟪ (Sw12 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ Sw12 ∷ []) ⟫ʷ
wn00359 b = win 0 3 b (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) _ _ Eq.refl
wn00360 : Base 3 → ⟪ (Sw12 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00360 b = win 0 3 b (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) _ _ Eq.refl
wn00361 : Base 3 → ⟪ (Sw12 ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ Sw12 ∷ []) ⟫ʷ
wn00361 b = win 0 3 b (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00362 : Base 3 → ⟪ (Sw12 ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00362 b = win 0 3 b (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) _ _ Eq.refl
wn00363 : Base 3 → ⟪ (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00363 b = win 3 0 b ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00364 : Base 3 → ⟪ (Sw12 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι2 ∷ Sw12 ∷ []) ⟫ʷ
wn00364 b = win 3 0 b ((Swap ↑) • (iI ↑)) ((iI ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00365 : Base 3 → ⟪ (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00365 b = win 0 3 b ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00366 : Base 3 → ⟪ (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00366 b = win 3 0 b ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00367 : Base 3 → ⟪ (K1 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K1 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00367 b = win 0 3 b (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00368 : Base 3 → ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00368 b = win 3 0 b ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00369 : Base 3 → ⟪ (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00369 b = win 0 3 b ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00370 : Base 3 → ⟪ (Sw23 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00370 b = win 0 3 b ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00371 : Base 3 → ⟪ (Sw23 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ Sw23 ∷ []) ⟫ʷ
wn00371 b = win 0 3 b ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00372 : Base 3 → ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ
wn00372 b = win 0 3 b ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) _ _ Eq.refl
wn00373 : Base 3 → ⟪ (Sw23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00373 b = win 0 3 b ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) _ _ Eq.refl
wn00374 : Base 3 → ⟪ (Sw23 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00374 b = win 0 3 b ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) _ _ Eq.refl
wn00375 : Base 3 → ⟪ (Sw23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw23 ∷ []) ⟫ʷ
wn00375 b = win 0 3 b ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) _ _ Eq.refl
wn00376 : Base 3 → ⟪ (Sw23 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Sw23 ∷ []) ⟫ʷ
wn00376 b = win 0 3 b ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) _ _ Eq.refl
wn00377 : Base 3 → ⟪ (Sw23 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw23 ∷ []) ⟫ʷ
wn00377 b = win 0 3 b ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) _ _ Eq.refl
wn00378 : Base 3 → ⟪ (Sw23 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw23 ∷ []) ⟫ʷ
wn00378 b = win 0 3 b ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00379 : Base 3 → ⟪ (Sw23 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ Sw23 ∷ []) ⟫ʷ
wn00379 b = win 0 3 b ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00380 : Base 3 → ⟪ (Sw23 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00380 b = win 0 3 b ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) _ _ Eq.refl
wn00381 : Base 3 → ⟪ (Sw23 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Sw23 ∷ []) ⟫ʷ
wn00381 b = win 0 3 b ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00382 : Base 3 → ⟪ (Sw23 ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ Sw23 ∷ []) ⟫ʷ
wn00382 b = win 0 3 b ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00383 : Base 3 → ⟪ (Sw23 ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00383 b = win 0 3 b ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) _ _ Eq.refl
wn00384 : Base 3 → ⟪ (K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00384 b = win 0 3 b (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00385 : Base 3 → ⟪ (K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00385 b = win 0 3 b ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00386 : Base 3 → ⟪ (K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00386 b = win 0 3 b ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00387 : Base 3 → ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00387 b = win 3 0 b (X • X) (ε) _ _ Eq.refl
wn00388 : Base 3 → ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00388 b = win 3 0 b ((X ↑) • (X ↑)) (ε) _ _ Eq.refl
wn00389 : Base 3 → ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00389 b = win 3 0 b ((X ↑ ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn00390 : Base 3 → ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00390 b = win 0 3 b ((X ↑ ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn00391 : Base 3 → ⟪ (X0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn00391 b = win 3 0 b (X • S • K) ((S • S • S) • (K • iI) • S • S) _ _ Eq.refl
wn00392 : Base 3 → ⟪ (K0⁻ ∷ S0⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn00392 b = win 3 0 b ((K • iI) • (S • S • S) • X) ((S • S • S) • (S • S • S) • K • S) _ _ Eq.refl
wn00393 : Base 3 → ⟪ (X2 ∷ S2 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ
wn00393 b = win 3 0 b ((X ↑ ↑) • (S ↑ ↑) • (K ↑ ↑)) (((S • S • S) ↑ ↑) • ((K • iI) ↑ ↑) • (S ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00394 : Base 3 → ⟪ (K2⁻ ∷ S2⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ
wn00394 b = win 3 0 b (((K • iI) ↑ ↑) • ((S • S • S) ↑ ↑) • (X ↑ ↑)) (((S • S • S) ↑ ↑) • ((S • S • S) ↑ ↑) • (K ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00395 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00395 b = win 0 3 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00396 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00396 b = win 0 3 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00397 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00397 b = win 0 3 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00398 : Base 3 → ⟪ (K2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1 ∷ []) ⟫ʷ
wn00398 b = win 3 0 b ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) _ _ Eq.refl
wn00399 : Base 3 → ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn00399 b = win 0 3 b ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00400 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00400 b = win 0 3 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00401 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00401 b = win 0 3 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00402 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00402 b = win 0 3 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00403 : Base 3 → ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00403 b = win 0 3 b ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00404 : Base 3 → ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn00404 b = win 0 3 b ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00405 : Base 3 → ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00405 b = win 0 3 b ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00406 : Base 3 → ⟪ (CS12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS12 ∷ []) ⟫ʷ
wn00406 b = win 0 3 b (CS • (CS ↑)) ((CS ↑) • CS) _ _ Eq.refl
wn00407 : Base 3 → ⟪ (CX21 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX21 ∷ []) ⟫ʷ
wn00407 b = win 0 3 b (CX₁₀ • (CS ↑)) ((CS ↑) • CX₁₀) _ _ Eq.refl
wn00408 : Base 3 → ⟪ (CS23 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS23 ∷ []) ⟫ʷ
wn00408 b = win 1 2 b ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
