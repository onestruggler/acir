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
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn00216 : ⟪ (CS01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS01 ∷ []) ⟫ʷ
wn00216 = win 3 0 complete₃ (CS • Swap) (Swap • CS) _ _ Eq.refl
wn00217 : ⟪ (X1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ X0 ∷ []) ⟫ʷ
wn00217 = win 3 0 complete₃ ((X ↑) • Swap) (Swap • X) _ _ Eq.refl
wn00218 : ⟪ (CK10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK01 ∷ []) ⟫ʷ
wn00218 = win 3 0 complete₃ (CK₁₀ • Swap) (Swap • CK₀₁) _ _ Eq.refl
wn00219 : ⟪ (Sw01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sw01 ∷ []) ⟫ʷ
wn00219 = win 3 0 complete₃ (Swap • CS) (CS • Swap) _ _ Eq.refl
wn00220 : ⟪ (Sw01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw01 ∷ []) ⟫ʷ
wn00220 = win 3 0 complete₃ (Swap • X) ((X ↑) • Swap) _ _ Eq.refl
wn00221 : ⟪ (Sw01 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ Sw01 ∷ []) ⟫ʷ
wn00221 = win 3 0 complete₃ (Swap • CK₀₁) (CK₁₀ • Swap) _ _ Eq.refl
wn00222 : ⟪ (Sw12 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw12 ∷ []) ⟫ʷ
wn00222 = win 3 0 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00223 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn00223 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00224 : ⟪ (K0 ∷ Toff012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00224 = win 3 0 complete₃ (K • Toff • (K • iI)) (CCZ) _ _ Eq.refl
wn00225 : ⟪ [] ⟫ʷ ≈ ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ
wn00225 = win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00226 : ⟪ (CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ []) ⟫ʷ
wn00226 = win 3 0 complete₃ (CCZ • (K • iI)) ((K • iI) • Toff) _ _ Eq.refl
wn00227 : ⟪ (Toff012 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00227 = win 3 0 complete₃ (Toff • Toff) (ε) _ _ Eq.refl
wn00228 : ⟪ (Toff012 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CCZ012 ∷ []) ⟫ʷ
wn00228 = win 3 0 complete₃ (Toff • K) (K • CCZ) _ _ Eq.refl
wn00229 : ⟪ (CS12 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00229 = win 3 0 complete₃ ((CS ↑) • (K • iI)) ((K • iI) • (CS ↑)) _ _ Eq.refl
wn00230 : ⟪ (CS12 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ []) ⟫ʷ
wn00230 = win 3 0 complete₃ ((CS ↑) • K) (K • (CS ↑)) _ _ Eq.refl
wn00231 : ⟪ [] ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00231 = win 3 0 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00232 : ⟪ [] ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ []) ⟫ʷ
wn00232 = win 3 0 complete₃ (ε) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00233 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn00233 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00234 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00234 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00235 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn00235 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00236 : ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ
wn00236 = win 3 0 complete₃ ((S • S • S) • CCZ) (CCZ • (S • S • S)) _ _ Eq.refl
wn00237 : ⟪ (S0 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ S0 ∷ []) ⟫ʷ
wn00237 = win 3 0 complete₃ (S • CCZ) (CCZ • S) _ _ Eq.refl
wn00238 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn00238 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00239 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn00239 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00240 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn00240 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00241 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
wn00241 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00242 : ⟪ (CS02 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS02 ∷ []) ⟫ʷ
wn00242 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (S ↑)) ((S ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00243 : ⟪ (CS02 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00243 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00244 : ⟪ (CS02 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00244 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00245 : ⟪ (CS02 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02 ∷ []) ⟫ʷ
wn00245 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00246 : ⟪ (CS02 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00246 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00247 : ⟪ (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00247 = win 3 0 complete₃ (Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00248 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
wn00248 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00249 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00249 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00250 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
wn00250 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00251 : ⟪ (CCZ012 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
wn00251 = win 3 0 complete₃ (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) _ _ Eq.refl
wn00252 : ⟪ [] ⟫ʷ ≈ ⟪ (CX02 ∷ CX02 ∷ []) ⟫ʷ
wn00252 = win 3 0 complete₃ (ε) ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00253 : ⟪ (CX12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX02 ∷ []) ⟫ʷ
wn00253 = win 3 0 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00254 : ⟪ (CCZ012 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00254 = win 3 0 complete₃ (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) _ _ Eq.refl
wn00255 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00255 = win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00256 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00256 = win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00257 : ⟪ (X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ []) ⟫ʷ
wn00257 = win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) _ _ Eq.refl
wn00258 : ⟪ (X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ []) ⟫ʷ
wn00258 = win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) _ _ Eq.refl
wn00259 : ⟪ (CCZ123 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ123 ∷ []) ⟫ʷ
wn00259 = win 0 3 complete₃ (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) _ _ Eq.refl
wn00260 : ⟪ (CCZ123 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn00260 = win 0 3 complete₃ (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) _ _ Eq.refl
wn00261 : ⟪ (CX20 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CX20 ∷ []) ⟫ʷ
wn00261 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00262 : ⟪ (CS02 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00262 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00263 : ⟪ (CS02 ∷ S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS02⁻ ∷ CS02 ∷ []) ⟫ʷ
wn00263 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00264 : ⟪ (CS02⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00264 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00265 : ⟪ (S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ S0 ∷ []) ⟫ʷ
wn00265 = win 3 0 complete₃ (S • CS) (CS • S) _ _ Eq.refl
wn00266 : ⟪ (CCZ123 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ123 ∷ []) ⟫ʷ
wn00266 = win 0 3 complete₃ (CCZ • (CS ↑)) ((CS ↑) • CCZ) _ _ Eq.refl
wn00267 : ⟪ (CCZ123 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ123 ∷ []) ⟫ʷ
wn00267 = win 0 3 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) _ _ Eq.refl
wn00268 : ⟪ (S0 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S0 ∷ []) ⟫ʷ
wn00268 = win 3 0 complete₃ (S • (CS • CS • CS)) ((CS • CS • CS) • S) _ _ Eq.refl
wn00269 : ⟪ (CCZ123 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ123 ∷ []) ⟫ʷ
wn00269 = win 0 3 complete₃ (CCZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00270 : ⟪ (CS02⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn00270 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00271 : ⟪ (K1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K0 ∷ []) ⟫ʷ
wn00271 = win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) _ _ Eq.refl
wn00272 : ⟪ (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00272 = win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00273 : ⟪ (CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK20 ∷ []) ⟫ʷ
wn00273 = win 3 0 complete₃ ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00274 : ⟪ (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00274 = win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00275 : ⟪ (Sw01 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ Sw01 ∷ []) ⟫ʷ
wn00275 = win 3 0 complete₃ (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) _ _ Eq.refl
wn00276 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn00276 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00277 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00277 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00278 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn00278 = win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00279 : ⟪ (CK31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK32 ∷ []) ⟫ʷ
wn00279 = win 0 3 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) _ _ Eq.refl
wn00280 : ⟪ (CK32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK31 ∷ []) ⟫ʷ
wn00280 = win 0 3 complete₃ ((CK₁₀ ↑) • Swap) (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00281 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn00281 = win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00282 : ⟪ (CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK32⁻ ∷ []) ⟫ʷ
wn00282 = win 0 3 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn00283 : ⟪ (CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CK31⁻ ∷ []) ⟫ʷ
wn00283 = win 0 3 complete₃ (((S ↑ • CK₁₀) ↑) • Swap) (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00284 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
wn00284 = win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00285 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00285 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00286 : ⟪ (CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ []) ⟫ʷ
wn00286 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00287 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00287 = win 0 3 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00288 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00288 = win 0 3 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn00289 : ⟪ (Toff012 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Toff012 ∷ []) ⟫ʷ
wn00289 = win 3 0 complete₃ (Toff • (S ↑)) ((S ↑) • Toff) _ _ Eq.refl
wn00290 : ⟪ (Toff012 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Toff012 ∷ []) ⟫ʷ
wn00290 = win 3 0 complete₃ (Toff • ((S • S • S) ↑)) (((S • S • S) ↑) • Toff) _ _ Eq.refl
wn00291 : ⟪ (CS02⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00291 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑)) ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00292 : ⟪ (CS02⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
wn00292 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00293 : ⟪ (Toff102 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff102 ∷ []) ⟫ʷ
wn00293 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00294 : ⟪ (S0 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ S0 ∷ []) ⟫ʷ
wn00294 = win 3 0 complete₃ (S • (CS ↑)) ((CS ↑) • S) _ _ Eq.refl
wn00295 : ⟪ (S0 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ S0 ∷ []) ⟫ʷ
wn00295 = win 3 0 complete₃ (S • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • S) _ _ Eq.refl
wn00296 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00296 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • Toff) (Toff • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00297 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00297 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00298 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn00298 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn00299 : ⟪ (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
wn00299 = win 3 0 complete₃ ((CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑)) _ _ Eq.refl
wn00300 : ⟪ (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00300 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00301 : ⟪ (CCZ012 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ012 ∷ []) ⟫ʷ
wn00301 = win 3 0 complete₃ (CCZ • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CCZ) _ _ Eq.refl
wn00302 : ⟪ (CS12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12 ∷ []) ⟫ʷ
wn00302 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00303 : ⟪ (CS12⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00303 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00304 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
wn00304 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00305 : ⟪ (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00305 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑)) ((X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00306 : ⟪ (S1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1 ∷ []) ⟫ʷ
wn00306 = win 0 3 complete₃ (S • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • S) _ _ Eq.refl
wn00307 : ⟪ (S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1 ∷ []) ⟫ʷ
wn00307 = win 0 3 complete₃ (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S) _ _ Eq.refl
wn00308 : ⟪ (S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1⁻ ∷ []) ⟫ʷ
wn00308 = win 0 3 complete₃ ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00309 : ⟪ (S1⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
wn00309 = win 0 3 complete₃ ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00310 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn00310 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00311 : ⟪ (Sw01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Sw01 ∷ []) ⟫ʷ
wn00311 = win 3 0 complete₃ (Swap • S) ((S ↑) • Swap) _ _ Eq.refl
wn00312 : ⟪ (Sw01 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00312 = win 3 0 complete₃ (Swap • (S • S • S)) (((S • S • S) ↑) • Swap) _ _ Eq.refl
wn00313 : ⟪ (Sw01 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00313 = win 3 0 complete₃ (Swap • (K • iI)) (((K • iI) ↑) • Swap) _ _ Eq.refl
wn00314 : ⟪ (Sw01 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Sw01 ∷ []) ⟫ʷ
wn00314 = win 3 0 complete₃ (Swap • Z) ((Z ↑) • Swap) _ _ Eq.refl
wn00315 : ⟪ (Sw01 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Sw01 ∷ []) ⟫ʷ
wn00315 = win 3 0 complete₃ (Swap • (S ↑)) (S • Swap) _ _ Eq.refl
wn00316 : ⟪ (Sw01 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00316 = win 3 0 complete₃ (Swap • ((S • S • S) ↑)) ((S • S • S) • Swap) _ _ Eq.refl
wn00317 : ⟪ (Sw01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sw01 ∷ []) ⟫ʷ
wn00317 = win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) _ _ Eq.refl
wn00318 : ⟪ (Sw01 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ Sw01 ∷ []) ⟫ʷ
wn00318 = win 3 0 complete₃ (Swap • (Z ↑)) (Z • Swap) _ _ Eq.refl
wn00319 : ⟪ (Sw01 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00319 = win 3 0 complete₃ (Swap • (CS • CS • CS)) ((CS • CS • CS) • Swap) _ _ Eq.refl
wn00320 : ⟪ (Sw01 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw01 ∷ []) ⟫ʷ
wn00320 = win 3 0 complete₃ (Swap • CZ) (CZ • Swap) _ _ Eq.refl
wn00321 : ⟪ (Sw01 ∷ CK01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00321 = win 3 0 complete₃ (Swap • (S • CK₀₁)) ((S ↑ • CK₁₀) • Swap) _ _ Eq.refl
wn00322 : ⟪ (Sw01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00322 = win 3 0 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) _ _ Eq.refl
wn00323 : ⟪ (Sw01 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw01 ∷ []) ⟫ʷ
wn00323 = win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) _ _ Eq.refl
wn00324 : ⟪ (Sw01 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ Sw01 ∷ []) ⟫ʷ
wn00324 = win 3 0 complete₃ (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) _ _ Eq.refl
wn00325 : ⟪ (Sw01 ∷ CK02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00325 = win 3 0 complete₃ (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) _ _ Eq.refl
wn00326 : ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ
wn00326 = win 3 0 complete₃ (Swap • CX₁₀) (CX₀₁ • Swap) _ _ Eq.refl
wn00327 : ⟪ (Sw01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ Sw01 ∷ []) ⟫ʷ
wn00327 = win 3 0 complete₃ (Swap • CK₁₀) (CK₀₁ • Swap) _ _ Eq.refl
wn00328 : ⟪ (Sw01 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00328 = win 3 0 complete₃ (Swap • (S ↑ • CK₁₀)) ((S • CK₀₁) • Swap) _ _ Eq.refl
wn00329 : ⟪ (Sw01 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ Sw01 ∷ []) ⟫ʷ
wn00329 = win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00330 : ⟪ (Sw01 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00330 = win 3 0 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) _ _ Eq.refl
wn00331 : ⟪ (Sw01 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Sw01 ∷ []) ⟫ʷ
wn00331 = win 3 0 complete₃ (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) _ _ Eq.refl
wn00332 : ⟪ (Sw01 ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00332 = win 3 0 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) _ _ Eq.refl
wn00333 : ⟪ (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00333 = win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00334 : ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00334 = win 0 3 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00335 : ⟪ (Sw23 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ Sw23 ∷ []) ⟫ʷ
wn00335 = win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00336 : ⟪ (Sw23 ∷ K3 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sw23 ∷ []) ⟫ʷ
wn00336 = win 0 3 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) _ _ Eq.refl
wn00337 : ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00337 = win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00338 : ⟪ (Sw12 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Sw12 ∷ []) ⟫ʷ
wn00338 = win 3 0 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00339 : ⟪ (Sw12 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00339 = win 3 0 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00340 : ⟪ (Sw12 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sw12 ∷ []) ⟫ʷ
wn00340 = win 3 0 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00341 : ⟪ (Sw12 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00341 = win 3 0 complete₃ ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00342 : ⟪ (Sw12 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Sw12 ∷ []) ⟫ʷ
wn00342 = win 3 0 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00343 : ⟪ (Sw12 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Sw12 ∷ []) ⟫ʷ
wn00343 = win 3 0 complete₃ ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) _ _ Eq.refl
wn00344 : ⟪ (Sw12 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00344 = win 3 0 complete₃ ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) _ _ Eq.refl
wn00345 : ⟪ (Sw12 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sw12 ∷ []) ⟫ʷ
wn00345 = win 3 0 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) _ _ Eq.refl
wn00346 : ⟪ (Sw12 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00346 = win 3 0 complete₃ ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) _ _ Eq.refl
wn00347 : ⟪ (Sw12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Sw12 ∷ []) ⟫ʷ
wn00347 = win 3 0 complete₃ ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) _ _ Eq.refl
wn00348 : ⟪ (Sw12 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Sw12 ∷ []) ⟫ʷ
wn00348 = win 3 0 complete₃ ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) _ _ Eq.refl
wn00349 : ⟪ (Sw12 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw12 ∷ []) ⟫ʷ
wn00349 = win 3 0 complete₃ ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) _ _ Eq.refl
wn00350 : ⟪ (Sw12 ∷ CK12 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ Sw12 ∷ []) ⟫ʷ
wn00350 = win 3 0 complete₃ ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00351 : ⟪ (Sw12 ∷ CK12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00351 = win 3 0 complete₃ ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) _ _ Eq.refl
wn00352 : ⟪ (Sw12 ∷ CK13 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ Sw12 ∷ []) ⟫ʷ
wn00352 = win 0 3 complete₃ (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) _ _ Eq.refl
wn00353 : ⟪ (Sw12 ∷ CK13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00353 = win 0 3 complete₃ (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) _ _ Eq.refl
wn00354 : ⟪ (Sw12 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Sw12 ∷ []) ⟫ʷ
wn00354 = win 3 0 complete₃ ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00355 : ⟪ (Sw12 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ Sw12 ∷ []) ⟫ʷ
wn00355 = win 3 0 complete₃ ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00356 : ⟪ (Sw12 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00356 = win 3 0 complete₃ ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) _ _ Eq.refl
wn00357 : ⟪ (Sw12 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ Sw12 ∷ []) ⟫ʷ
wn00357 = win 0 3 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00358 : ⟪ (Sw12 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00358 = win 0 3 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) _ _ Eq.refl
wn00359 : ⟪ (Sw12 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ Sw12 ∷ []) ⟫ʷ
wn00359 = win 0 3 complete₃ (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) _ _ Eq.refl
wn00360 : ⟪ (Sw12 ∷ CK31⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00360 = win 0 3 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) _ _ Eq.refl
wn00361 : ⟪ (Sw12 ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ Sw12 ∷ []) ⟫ʷ
wn00361 = win 0 3 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00362 : ⟪ (Sw12 ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00362 = win 0 3 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) _ _ Eq.refl
wn00363 : ⟪ (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00363 = win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00364 : ⟪ (Sw12 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι2 ∷ Sw12 ∷ []) ⟫ʷ
wn00364 = win 3 0 complete₃ ((Swap ↑) • (iI ↑)) ((iI ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00365 : ⟪ (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00365 = win 0 3 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00366 : ⟪ (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00366 = win 3 0 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00367 : ⟪ (K1 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K1 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00367 = win 0 3 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00368 : ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ⟫ʷ
wn00368 = win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00369 : ⟪ (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ ι2 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00369 = win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑ ↑) • (iI ↑)) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00370 : ⟪ (Sw23 ∷ K2⁻ ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00370 = win 0 3 complete₃ ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00371 : ⟪ (Sw23 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ Sw23 ∷ []) ⟫ʷ
wn00371 = win 0 3 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00372 : ⟪ (Sw23 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Sw23 ∷ []) ⟫ʷ
wn00372 = win 0 3 complete₃ ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) _ _ Eq.refl
wn00373 : ⟪ (Sw23 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00373 = win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) _ _ Eq.refl
wn00374 : ⟪ (Sw23 ∷ K3⁻ ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00374 = win 0 3 complete₃ ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) _ _ Eq.refl
wn00375 : ⟪ (Sw23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Sw23 ∷ []) ⟫ʷ
wn00375 = win 0 3 complete₃ ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) _ _ Eq.refl
wn00376 : ⟪ (Sw23 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Sw23 ∷ []) ⟫ʷ
wn00376 = win 0 3 complete₃ ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) _ _ Eq.refl
wn00377 : ⟪ (Sw23 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw23 ∷ []) ⟫ʷ
wn00377 = win 0 3 complete₃ ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) _ _ Eq.refl
wn00378 : ⟪ (Sw23 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw23 ∷ []) ⟫ʷ
wn00378 = win 0 3 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00379 : ⟪ (Sw23 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ Sw23 ∷ []) ⟫ʷ
wn00379 = win 0 3 complete₃ ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00380 : ⟪ (Sw23 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00380 = win 0 3 complete₃ ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) _ _ Eq.refl
wn00381 : ⟪ (Sw23 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Sw23 ∷ []) ⟫ʷ
wn00381 = win 0 3 complete₃ ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00382 : ⟪ (Sw23 ∷ CK32 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ Sw23 ∷ []) ⟫ʷ
wn00382 = win 0 3 complete₃ ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) _ _ Eq.refl
wn00383 : ⟪ (Sw23 ∷ CK32⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00383 = win 0 3 complete₃ ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) _ _ Eq.refl
wn00384 : ⟪ (K1 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00384 = win 0 3 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00385 : ⟪ (K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ⟫ʷ
wn00385 = win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) _ _ Eq.refl
wn00386 : ⟪ (K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ⟫ʷ
wn00386 = win 0 3 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00387 : ⟪ (X0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00387 = win 3 0 complete₃ (X • X) (ε) _ _ Eq.refl
wn00388 : ⟪ (X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00388 = win 3 0 complete₃ ((X ↑) • (X ↑)) (ε) _ _ Eq.refl
wn00389 : ⟪ (X2 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00389 = win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn00390 : ⟪ (X3 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00390 = win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
wn00391 : ⟪ (X0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn00391 = win 3 0 complete₃ (X • S • K) ((S • S • S) • (K • iI) • S • S) _ _ Eq.refl
wn00392 : ⟪ (K0⁻ ∷ S0⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn00392 = win 3 0 complete₃ ((K • iI) • (S • S • S) • X) ((S • S • S) • (S • S • S) • K • S) _ _ Eq.refl
wn00393 : ⟪ (X2 ∷ S2 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ
wn00393 = win 3 0 complete₃ ((X ↑ ↑) • (S ↑ ↑) • (K ↑ ↑)) (((S • S • S) ↑ ↑) • ((K • iI) ↑ ↑) • (S ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00394 : ⟪ (K2⁻ ∷ S2⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ
wn00394 = win 3 0 complete₃ (((K • iI) ↑ ↑) • ((S • S • S) ↑ ↑) • (X ↑ ↑)) (((S • S • S) ↑ ↑) • ((S • S • S) ↑ ↑) • (K ↑ ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00395 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00395 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00396 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00396 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00397 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00397 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00398 : ⟪ (K2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ K1 ∷ []) ⟫ʷ
wn00398 = win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) _ _ Eq.refl
wn00399 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn00399 = win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00400 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00400 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00401 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00401 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • CS) (CS • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00402 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00402 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (CS • CS • CS)) ((CS • CS • CS) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00403 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn00403 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00404 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn00404 = win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00405 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn00405 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • Toff) (Toff • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn00406 : ⟪ (CS12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS12 ∷ []) ⟫ʷ
wn00406 = win 0 3 complete₃ (CS • (CS ↑)) ((CS ↑) • CS) _ _ Eq.refl
wn00407 : ⟪ (CX21 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX21 ∷ []) ⟫ʷ
wn00407 = win 0 3 complete₃ (CX₁₀ • (CS ↑)) ((CS ↑) • CX₁₀) _ _ Eq.refl
wn00408 : ⟪ (CS23 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS23 ∷ []) ⟫ʷ
wn00408 = win 1 2 complete₃ ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
