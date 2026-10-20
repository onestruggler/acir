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

module Examples.Groups.Clifford+CS.Four.Wins.W47 where

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

wn02345 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
wn02345 = win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • (CK₀₁ ↑) • (X ↑)) _ _ Eq.refl
wn02346 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02346 = win 1 2 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • X • (X ↑)) (X • (X ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02347 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02347 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02348 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02348 = win 0 3 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02349 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
wn02349 = win 1 2 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • X • (X ↑)) (X • (X ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02350 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02350 = win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X • (X ↑)) (X • (X ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02351 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02351 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02352 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
wn02352 = win 0 3 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02353 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
wn02353 = win 1 2 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • X • (X ↑)) (X • (X ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02354 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02354 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02355 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
wn02355 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02356 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
wn02356 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02357 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
wn02357 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02358 : ⟪ (K0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02358 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (K • iI) • S • S) (S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02359 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02359 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • S) (S • K • (S • S • S) • (K • iI)) _ _ Eq.refl
wn02360 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02360 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02361 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02361 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • S • K) (S • K • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02362 : ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02362 = win 3 0 complete₃ ((K • iI) • (K • iI) • (K • iI)) ((K • iI) • (K • iI) • (K • iI)) _ _ Eq.refl
wn02363 : ⟪ (K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02363 = win 3 0 complete₃ (K • K) (K • K • K • (K • iI)) _ _ Eq.refl
wn02364 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02364 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S • (K • iI) • S) (S • (K • iI) • S • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02365 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02365 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (S • S • S) • K • (S • S • S)) ((S • S • S) • K • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02366 : ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02366 = win 3 0 complete₃ (K • S • S • (K • iI) • S) ((S • S • S) • (K • iI) • S • S • (K • iI)) _ _ Eq.refl
wn02367 : ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02367 = win 3 0 complete₃ ((S • S • S) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • K • S • K) _ _ Eq.refl
wn02368 : ⟪ (K0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
wn02368 = win 3 0 complete₃ (K • (S • S • S) • (K • iI) • S • S • (K • iI)) (S • S • K • S) _ _ Eq.refl
wn02369 : ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02369 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • K) _ _ Eq.refl
wn02370 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02370 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • S • S • K • S) (S • S • K • S • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02371 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
wn02371 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02372 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02372 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • S • S • K • S • S) (S • S • K • S • S • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02373 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02373 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S)) ((S • S • S) • (S • S • S) • (K • iI) • (S • S • S) • (S • S • S) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02374 : ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02374 = win 3 0 complete₃ (K • (S • S • S) • K • S • S) (S • K • (S • S • S) • K • K) _ _ Eq.refl
wn02375 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02375 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • (K • iI) • S) ((K • iI) • (K • iI) • S • (K • iI) • (S • S • S) • K) _ _ Eq.refl
wn02376 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02376 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • S • (K • iI)) (S • S • (K • iI) • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02377 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02377 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • K • (S • S • S) • (S • S • S)) (K • (S • S • S) • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02378 : ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02378 = win 3 0 complete₃ ((K • iI) • S • (K • iI)) ((K • iI) • S • (K • iI)) _ _ Eq.refl
wn02379 : ⟪ (K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02379 = win 3 0 complete₃ (K • (S • S • S)) (K • (S • S • S) • K • (K • iI)) _ _ Eq.refl
wn02380 : ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02380 = win 3 0 complete₃ (S • (K • iI) • S • (K • iI)) (S • (K • iI) • S • (K • iI)) _ _ Eq.refl
wn02381 : ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02381 = win 3 0 complete₃ (K • (S • S • S) • K) (K • (S • S • S) • K • (S • S • S) • S) _ _ Eq.refl
wn02382 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02382 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • S • S • K • K • K • K) (S • S • K • K • K • K • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02383 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02383 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (K • iI) • (K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) ((K • iI) • (K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02384 : ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn02384 = win 3 0 complete₃ (S • S • (K • iI) • S • (K • iI) • (S • S • S)) (S • S • (K • iI) • S • (K • iI) • (S • S • S)) _ _ Eq.refl
wn02385 : ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02385 = win 3 0 complete₃ (S • K • (S • S • S) • K • (S • S • S)) (S • K • (S • S • S) • K • (S • S • S) • (S • S • S) • S) _ _ Eq.refl
wn02386 : ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ
wn02386 = win 3 0 complete₃ ((K • iI) • S • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) _ _ Eq.refl
wn02387 : ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ
wn02387 = win 3 0 complete₃ ((S • S • S) • (S • S • S) • K • (S • S • S)) (K • K • (S • S • S) • K • S • (K • iI)) _ _ Eq.refl
wn02388 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02388 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • (K • iI) • (K • iI)) ((S • S • S) • (K • iI) • S • (K • iI) • (K • iI) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02389 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02389 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • K • (S • S • S) • K • S) (K • K • (S • S • S) • K • S • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02390 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02390 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • S • S • (K • iI) • S • (K • iI) • (K • iI)) (S • S • (K • iI) • S • (K • iI) • (K • iI) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02391 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02391 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • K • K • (S • S • S) • K • (S • S • S) • (S • S • S)) (K • K • (S • S • S) • K • (S • S • S) • (S • S • S) • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02392 : ⟪ (S0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02392 = win 3 0 complete₃ (S • (S • S • S) • K • S • S • K) (K • S • S • K) _ _ Eq.refl
wn02393 : ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02393 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S) ((K • iI) • (S • S • S) • (S • S • S) • (K • iI) • S) _ _ Eq.refl
wn02394 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02394 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • S • S • K • K • K) (S • S • K • K • K • (X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02395 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02395 = win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • (K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S)) ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (S • S • S) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02396 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02396 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • S • K • K • K) (S • K • K • K • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02397 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02397 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (K • iI) • (K • iI) • (K • iI) • (S • S • S)) ((K • iI) • (K • iI) • (K • iI) • (S • S • S) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02398 : ⟪ (S0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) ⟫ʷ
wn02398 = win 3 0 complete₃ (S • (S • S • S) • K • (S • S • S) • K • K) (K • (S • S • S) • K • K) _ _ Eq.refl
wn02399 : ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02399 = win 3 0 complete₃ ((K • iI) • (K • iI) • S • (K • iI) • S) ((K • iI) • (K • iI) • S • (K • iI) • S) _ _ Eq.refl
wn02400 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
wn02400 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (S • S • S)) ((S • S • S) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) _ _ Eq.refl
wn02401 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02401 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • (CS • CS • CS) • (X ↑) • S) (S • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02402 : ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02402 = win 0 3 complete₃ (Swap • (Swap ↑) • Swap • Swap • (Swap ↑) • Swap) (ε) _ _ Eq.refl
wn02403 : ⟪ (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02403 = win 3 0 complete₃ ((K • iI) • (S • S • S) • K • (K • iI) • S • K) (ε) _ _ Eq.refl
wn02404 : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02404 = win 3 0 complete₃ ((K • iI) • S • K • (K • iI) • (S • S • S) • K) (ε) _ _ Eq.refl
wn02405 : ⟪ (Sw12 ∷ CCZ123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn02405 = win 0 3 complete₃ (Swap • CCZ • Swap) (CCZ) _ _ Eq.refl
wn02406 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0⁻ ∷ []) ⟫ʷ
wn02406 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn02407 : ⟪ (Toff012 ∷ S0 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn02407 = win 3 0 complete₃ (Toff • S • Toff) (S • (CS ↑) • CCZ) _ _ Eq.refl
wn02408 : ⟪ (S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn02408 = win 3 0 complete₃ (S • S • K) (S • S • K) _ _ Eq.refl
wn02409 : ⟪ (K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ S0 ∷ []) ⟫ʷ
wn02409 = win 3 0 complete₃ ((K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (S • S • S) • S) _ _ Eq.refl
wn02410 : ⟪ (S0 ∷ S0 ∷ S0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ []) ⟫ʷ
wn02410 = win 3 0 complete₃ (S • S • S • K) ((S • S • S) • K) _ _ Eq.refl
wn02411 : ⟪ (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ
wn02411 = win 3 0 complete₃ ((K • iI) • (S • S • S) • (S • S • S)) ((K • iI) • S • S) _ _ Eq.refl
wn02412 : ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
wn02412 = win 0 3 complete₃ (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑)) _ _ Eq.refl
wn02413 : ⟪ (S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
wn02413 = win 0 3 complete₃ (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02414 : ⟪ (CS23⁻ ∷ CK32⁻ ∷ CS23 ∷ CS23 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02414 = win 0 3 complete₃ (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) (ε) _ _ Eq.refl
wn02415 : ⟪ (CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02415 = win 3 0 complete₃ ((S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02416 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ []) ⟫ʷ
wn02416 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02417 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02417 = win 3 0 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02418 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
wn02418 = win 3 0 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • CK₁₀ • (X ↑)) _ _ Eq.refl
wn02419 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02419 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (S • S • S) • (K • iI) • S • S) ((S • S • S) • (K • iI) • S • S • (X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02420 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
wn02420 = win 3 0 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑) • CS • (X ↑) • (S • S • S) • (S • S • S) • K • S) ((S • S • S) • (S • S • S) • K • S • (X ↑) • CS • (X ↑)) _ _ Eq.refl
wn02421 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02421 = win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02422 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
wn02422 = win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02423 : ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CK21 ∷ CS13⁻ ∷ CK21⁻ ∷ []) ⟫ʷ
wn02423 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) _ _ Eq.refl
wn02424 : ⟪ (CS13 ∷ CK21 ∷ CS13⁻ ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ
wn02424 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CK₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ • CK₁₀)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑) • CS • CS • CS • CS • CS • CS • CK₁₀ • (S ↑) • CS • CS • CS • CS • CS • CS • CS • CS • CS • (CX₁₀ ↑) • CS • CS • CS • CK₁₀ • CS • CS) _ _ Eq.refl
wn02425 : ⟪ (Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) ⟫ʷ
wn02425 = win 0 3 complete₃ (Toffᵗ) ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) _ _ Eq.refl
wn02426 : ⟪ (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ []) ⟫ʷ
wn02426 = win 0 3 complete₃ ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) (Toffᵗ) _ _ Eq.refl
wn02427 : ⟪ (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ []) ⟫ʷ
wn02427 = win 3 0 complete₃ (K • S • S • (K • iI)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn02428 : ⟪ (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
wn02428 = win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • (K • iI)) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02429 : ⟪ (CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ CK20 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02429 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (ε) _ _ Eq.refl
wn02430 : ⟪ (CK10 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
wn02430 = win 3 0 complete₃ (CK₁₀) (K • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) _ _ Eq.refl
wn02431 : ⟪ (K0 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
wn02431 = win 3 0 complete₃ (K • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) (CK₁₀) _ _ Eq.refl
wn02432 : ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
wn02432 = win 0 3 complete₃ (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn02433 : ⟪ (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) ⟫ʷ
wn02433 = win 0 3 complete₃ (CK₁₀ • (Swap ↑ • CS • Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (CS • CS • CK₁₀ • CS • CK₁₀ • CK₁₀ • (CX₀₁ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn02434 : ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
wn02434 = win 3 0 complete₃ (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) _ _ Eq.refl
wn02435 : ⟪ (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ
wn02435 = win 3 0 complete₃ (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) _ _ Eq.refl
wn02436 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn02436 = win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) (ε) _ _ Eq.refl
