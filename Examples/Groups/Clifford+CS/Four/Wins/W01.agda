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

module Examples.Groups.Clifford+CS.Four.Wins.W01 where

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

wn00001 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ
wn00001 b = win 0 3 b (ε) ((Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00002 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX20 ∷ CX20 ∷ []) ⟫ʷ
wn00002 b = win 3 0 b (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00003 : Base 3 → ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00003 b = win 0 3 b ((Swap ↑) • (Swap ↑)) (ε) _ _ Eq.refl
wn00004 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ
wn00004 b = win 3 0 b (ε) (CCZ • CCZ) _ _ Eq.refl
wn00005 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ
wn00005 b = win 3 0 b (ε) (Swap • Swap) _ _ Eq.refl
wn00006 : Base 3 → ⟪ (CX20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ []) ⟫ʷ
wn00006 b = win 3 0 b ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) _ _ Eq.refl
wn00007 : Base 3 → ⟪ (CS02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12 ∷ []) ⟫ʷ
wn00007 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) _ _ Eq.refl
wn00008 : Base 3 → ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ
wn00008 b = win 3 0 b (CX₀₁ • Swap) (Swap • CX₁₀) _ _ Eq.refl
wn00009 : Base 3 → ⟪ (CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00009 b = win 3 0 b (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00010 : Base 3 → ⟪ (CS12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02 ∷ []) ⟫ʷ
wn00010 b = win 3 0 b ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00011 : Base 3 → ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00011 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00012 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ
wn00012 b = win 3 0 b (ε) ((Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00013 : Base 3 → ⟪ (CX31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX32 ∷ []) ⟫ʷ
wn00013 b = win 0 3 b ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) _ _ Eq.refl
wn00014 : Base 3 → ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00014 b = win 3 0 b ((Swap ↑) • (Swap ↑)) (ε) _ _ Eq.refl
wn00015 : Base 3 → ⟪ (CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00015 b = win 3 0 b (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00016 : Base 3 → ⟪ (CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12 ∷ []) ⟫ʷ
wn00016 b = win 3 0 b ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00017 : Base 3 → ⟪ (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00017 b = win 3 0 b ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00018 : Base 3 → ⟪ (Sw12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw12 ∷ []) ⟫ʷ
wn00018 b = win 3 0 b ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) _ _ Eq.refl
wn00019 : Base 3 → ⟪ (Sw12 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00019 b = win 3 0 b ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) _ _ Eq.refl
wn00020 : Base 3 → ⟪ (Sw12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw12 ∷ []) ⟫ʷ
wn00020 b = win 0 3 b (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) _ _ Eq.refl
wn00021 : Base 3 → ⟪ (Sw12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00021 b = win 0 3 b (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) _ _ Eq.refl
wn00022 : Base 3 → ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
wn00022 b = win 0 3 b (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) _ _ Eq.refl
wn00023 : Base 3 → ⟪ (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ
wn00023 b = win 0 3 b ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) _ _ Eq.refl
wn00024 : Base 3 → ⟪ (Sw01 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Sw01 ∷ []) ⟫ʷ
wn00024 b = win 3 0 b (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) _ _ Eq.refl
wn00025 : Base 3 → ⟪ (Sw01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw01 ∷ []) ⟫ʷ
wn00025 b = win 3 0 b (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) _ _ Eq.refl
wn00026 : Base 3 → ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00026 b = win 0 3 b ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00027 : Base 3 → ⟪ (Sw01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw01 ∷ []) ⟫ʷ
wn00027 b = win 3 0 b (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) _ _ Eq.refl
wn00028 : Base 3 → ⟪ (Sw01 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sw01 ∷ []) ⟫ʷ
wn00028 b = win 3 0 b (Swap • CX₀₁) (CX₁₀ • Swap) _ _ Eq.refl
wn00029 : Base 3 → ⟪ (Sw01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00029 b = win 3 0 b (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) _ _ Eq.refl
wn00030 : Base 3 → ⟪ (Sw01 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Sw01 ∷ []) ⟫ʷ
wn00030 b = win 3 0 b (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00031 : Base 3 → ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00031 b = win 3 0 b (Swap • Swap) (ε) _ _ Eq.refl
wn00032 : Base 3 → ⟪ (CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00032 b = win 3 0 b (CCZ • CCZ) (ε) _ _ Eq.refl
wn00033 : Base 3 → ⟪ (CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00033 b = win 0 3 b (CCZ • CCZ) (ε) _ _ Eq.refl
wn00034 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00034 b = win 0 3 b (CCZ) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00035 : Base 3 → ⟪ (CS12 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CS12 ∷ []) ⟫ʷ
wn00035 b = win 3 0 b ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00036 : Base 3 → ⟪ (CX13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX23 ∷ []) ⟫ʷ
wn00036 b = win 0 3 b ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) _ _ Eq.refl
wn00037 : Base 3 → ⟪ (CX23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX13 ∷ []) ⟫ʷ
wn00037 b = win 0 3 b ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00038 : Base 3 → ⟪ (CS23⁻ ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00038 b = win 0 3 b (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00039 : Base 3 → ⟪ (Sw01 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sw01 ∷ []) ⟫ʷ
wn00039 b = win 3 0 b (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00040 : Base 3 → ⟪ (CS23 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS23 ∷ []) ⟫ʷ
wn00040 b = win 0 3 b ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00041 : Base 3 → ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00041 b = win 0 3 b ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00042 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX23 ∷ CX23 ∷ []) ⟫ʷ
wn00042 b = win 0 3 b (ε) ((CX₀₁ ↑) • (CX₀₁ ↑)) _ _ Eq.refl
wn00043 : Base 3 → ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00043 b = win 3 0 b ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00044 : Base 3 → ⟪ (CX23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX32 ∷ []) ⟫ʷ
wn00044 b = win 0 3 b ((CX₀₁ ↑) • (Swap ↑)) ((Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00045 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff012 ∷ []) ⟫ʷ
wn00045 b = win 3 0 b (ε) (Toff • Toff) _ _ Eq.refl
wn00046 : Base 3 → ⟪ (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00046 b = win 3 0 b (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00047 : Base 3 → ⟪ (CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00047 b = win 0 3 b (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00048 : Base 3 → ⟪ (CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13 ∷ []) ⟫ʷ
wn00048 b = win 0 3 b ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00049 : Base 3 → ⟪ (Sw12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw12 ∷ []) ⟫ʷ
wn00049 b = win 0 3 b (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) _ _ Eq.refl
wn00050 : Base 3 → ⟪ (Sw12 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Sw12 ∷ []) ⟫ʷ
wn00050 b = win 3 0 b ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00051 : Base 3 → ⟪ (Sw12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00051 b = win 0 3 b (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) _ _ Eq.refl
wn00052 : Base 3 → ⟪ (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00052 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00053 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ
wn00053 b = win 3 0 b (Toff) (K • CCZ • (K • iI)) _ _ Eq.refl
wn00054 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0 ∷ []) ⟫ʷ
wn00054 b = win 3 0 b (ε) ((K • iI) • K) _ _ Eq.refl
wn00055 : Base 3 → ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00055 b = win 3 0 b (K • CCZ • (K • iI)) (Toff) _ _ Eq.refl
wn00056 : Base 3 → ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00056 b = win 3 0 b (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00057 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ
wn00057 b = win 3 0 b (Toff) (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI)) _ _ Eq.refl
wn00058 : Base 3 → ⟪ (CX23 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CX23 ∷ []) ⟫ʷ
wn00058 b = win 0 3 b ((CX₀₁ ↑) • CX₁₀) (CX₁₀ • (CX₀₁ ↑)) _ _ Eq.refl
wn00059 : Base 3 → ⟪ (CX23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX23 ∷ []) ⟫ʷ
wn00059 b = win 0 3 b ((CX₀₁ ↑) • CS) (CS • (CX₀₁ ↑)) _ _ Eq.refl
wn00060 : Base 3 → ⟪ (CX23 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00060 b = win 0 3 b ((CX₀₁ ↑) • (CX₀₁ ↑)) (ε) _ _ Eq.refl
wn00061 : Base 3 → ⟪ (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00061 b = win 3 0 b (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI)) (Toff) _ _ Eq.refl
wn00062 : Base 3 → ⟪ (Sw23 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Sw23 ∷ []) ⟫ʷ
wn00062 b = win 0 3 b ((Swap ↑) • CX₁₀) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00063 : Base 3 → ⟪ (Sw23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw23 ∷ []) ⟫ʷ
wn00063 b = win 0 3 b ((Swap ↑) • CS) ((Swap ↑ • CS • Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00064 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) ⟫ʷ
wn00064 b = win 3 0 b (Toff) (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) _ _ Eq.refl
wn00065 : Base 3 → ⟪ (CS13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23 ∷ []) ⟫ʷ
wn00065 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) _ _ Eq.refl
wn00066 : Base 3 → ⟪ (CS13 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00066 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00067 : Base 3 → ⟪ (CS12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS12 ∷ []) ⟫ʷ
wn00067 b = win 3 0 b ((CS ↑) • CS) (CS • (CS ↑)) _ _ Eq.refl
wn00068 : Base 3 → ⟪ (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00068 b = win 3 0 b (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) (Toff) _ _ Eq.refl
wn00069 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX10 ∷ CX10 ∷ []) ⟫ʷ
wn00069 b = win 3 0 b (ε) (CX₁₀ • CX₁₀) _ _ Eq.refl
wn00070 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ
wn00070 b = win 0 3 b (ε) (CCZ • CCZ) _ _ Eq.refl
wn00071 : Base 3 → ⟪ (Sw23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw23 ∷ []) ⟫ʷ
wn00071 b = win 0 3 b ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) _ _ Eq.refl
wn00072 : Base 3 → ⟪ (Sw23 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00072 b = win 0 3 b ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) _ _ Eq.refl
wn00073 : Base 3 → ⟪ (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00073 b = win 0 3 b ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00074 : Base 3 → ⟪ (CX02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ []) ⟫ʷ
wn00074 b = win 3 0 b ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) _ _ Eq.refl
wn00075 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) ⟫ʷ
wn00075 b = win 0 3 b (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00076 : Base 3 → ⟪ (CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00076 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00077 : Base 3 → ⟪ (CS23 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00077 b = win 0 3 b ((CS ↑) • (CS • CS • CS)) ((CS • CS • CS) • (CS ↑)) _ _ Eq.refl
wn00078 : Base 3 → ⟪ (CX32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX31 ∷ []) ⟫ʷ
wn00078 b = win 0 3 b ((CX₁₀ ↑) • Swap) (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00079 : Base 3 → ⟪ (CS12⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00079 b = win 3 0 b (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00080 : Base 3 → ⟪ (CS12 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00080 b = win 3 0 b ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00081 : Base 3 → ⟪ (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00081 b = win 0 3 b (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) _ _ Eq.refl
wn00082 : Base 3 → ⟪ (CS23 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00082 b = win 0 3 b ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00083 : Base 3 → ⟪ (CX21 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CX21 ∷ []) ⟫ʷ
wn00083 b = win 3 0 b ((CX₁₀ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00084 : Base 3 → ⟪ (CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00084 b = win 0 3 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00085 : Base 3 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ
wn00085 b = win 3 0 b (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00086 : Base 3 → ⟪ (CS12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00086 b = win 0 3 b (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) _ _ Eq.refl
wn00087 : Base 3 → ⟪ (CS01⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn00087 b = win 3 0 b ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00088 : Base 3 → ⟪ (CS01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01 ∷ []) ⟫ʷ
wn00088 b = win 3 0 b (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) _ _ Eq.refl
wn00089 : Base 3 → ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00089 b = win 3 0 b (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00090 : Base 3 → ⟪ (CS12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12 ∷ []) ⟫ʷ
wn00090 b = win 3 0 b ((CS ↑) • Toff) (Toff • (CS ↑)) _ _ Eq.refl
wn00091 : Base 3 → ⟪ (CS23 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS23 ∷ []) ⟫ʷ
wn00091 b = win 0 3 b ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00092 : Base 3 → ⟪ (CX21 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX21 ∷ []) ⟫ʷ
wn00092 b = win 3 0 b ((CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00093 : Base 3 → ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ
wn00093 b = win 0 3 b (CS • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CS) _ _ Eq.refl
wn00094 : Base 3 → ⟪ (CS01⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00094 b = win 3 0 b ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00095 : Base 3 → ⟪ (CS01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01 ∷ []) ⟫ʷ
wn00095 b = win 3 0 b (CS • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CS) _ _ Eq.refl
wn00096 : Base 3 → ⟪ (CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ23 ∷ []) ⟫ʷ
wn00096 b = win 0 3 b ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) _ _ Eq.refl
wn00097 : Base 3 → ⟪ (CZ23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ13 ∷ []) ⟫ʷ
wn00097 b = win 0 3 b ((CZ ↑) • Swap) (Swap • (Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn00098 : Base 3 → ⟪ (CZ13 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CZ13 ∷ []) ⟫ʷ
wn00098 b = win 0 3 b ((Swap ↑ • CZ • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn00099 : Base 3 → ⟪ (CZ12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CZ12 ∷ []) ⟫ʷ
wn00099 b = win 3 0 b ((CZ ↑) • CS) (CS • (CZ ↑)) _ _ Eq.refl
wn00100 : Base 3 → ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) ⟫ʷ
wn00100 b = win 3 0 b (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00101 : Base 3 → ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ
wn00101 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00102 : Base 3 → ⟪ (CS01⁻ ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00102 b = win 3 0 b ((CS • CS • CS) • (CS ↑)) ((CS ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00103 : Base 3 → ⟪ (CS01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS01 ∷ []) ⟫ʷ
wn00103 b = win 3 0 b (CS • (CS ↑)) ((CS ↑) • CS) _ _ Eq.refl
wn00104 : Base 3 → ⟪ (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00104 b = win 3 0 b (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) _ _ Eq.refl
wn00105 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX32 ∷ CX32 ∷ []) ⟫ʷ
wn00105 b = win 0 3 b (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00106 : Base 3 → ⟪ (CS12 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS12 ∷ []) ⟫ʷ
wn00106 b = win 0 3 b (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) _ _ Eq.refl
wn00107 : Base 3 → ⟪ (Sw12 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw12 ∷ []) ⟫ʷ
wn00107 b = win 0 3 b (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) _ _ Eq.refl
wn00108 : Base 3 → ⟪ (Sw12 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Sw12 ∷ []) ⟫ʷ
wn00108 b = win 0 3 b (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) _ _ Eq.refl
wn00109 : Base 3 → ⟪ (CS01⁻ ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00109 b = win 3 0 b ((CS • CS • CS) • (CZ ↑)) ((CZ ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00110 : Base 3 → ⟪ (CS01 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS01 ∷ []) ⟫ʷ
wn00110 b = win 3 0 b (CS • (CZ ↑)) ((CZ ↑) • CS) _ _ Eq.refl
wn00111 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX31 ∷ CX31 ∷ []) ⟫ʷ
wn00111 b = win 0 3 b (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00112 : Base 3 → ⟪ (CX20 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CX20 ∷ []) ⟫ʷ
wn00112 b = win 3 0 b ((Swap ↑ • CX₁₀ • Swap ↑) • (CX₁₀ ↑)) ((CX₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00113 : Base 3 → ⟪ (Sw12 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw12 ∷ []) ⟫ʷ
wn00113 b = win 0 3 b (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) _ _ Eq.refl
wn00114 : Base 3 → ⟪ (Sw12 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Sw12 ∷ []) ⟫ʷ
wn00114 b = win 0 3 b (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00115 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (CX13 ∷ CX13 ∷ []) ⟫ʷ
wn00115 b = win 0 3 b (ε) ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00116 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ K0⁻ ∷ []) ⟫ʷ
wn00116 b = win 3 0 b (ε) (K • (K • iI)) _ _ Eq.refl
wn00117 : Base 3 → ⟪ (K0⁻ ∷ CK10 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
wn00117 b = win 3 0 b ((K • iI) • CK₁₀ • K) (CK₁₀) _ _ Eq.refl
wn00118 : Base 3 → ⟪ (K0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1 ∷ []) ⟫ʷ
wn00118 b = win 3 0 b (K • Swap) (Swap • (K ↑)) _ _ Eq.refl
wn00119 : Base 3 → ⟪ (K0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1⁻ ∷ []) ⟫ʷ
wn00119 b = win 3 0 b ((K • iI) • Swap) (Swap • ((K • iI) ↑)) _ _ Eq.refl
wn00120 : Base 3 → ⟪ (K1⁻ ∷ CCZ123 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn00120 b = win 0 3 b ((K • iI) • CCZ • K) (Toff) _ _ Eq.refl
wn00121 : Base 3 → ⟪ (Sw01 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sw01 ∷ []) ⟫ʷ
wn00121 b = win 3 0 b (Swap • (K ↑)) (K • Swap) _ _ Eq.refl
wn00122 : Base 3 → ⟪ (Sw01 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ
wn00122 b = win 3 0 b (Swap • (iI ↑)) (iI • Swap) _ _ Eq.refl
wn00123 : Base 3 → ⟪ (Sw01 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sw01 ∷ []) ⟫ʷ
wn00123 b = win 3 0 b (Swap • K) ((K ↑) • Swap) _ _ Eq.refl
wn00124 : Base 3 → ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ Sw01 ∷ []) ⟫ʷ
wn00124 b = win 3 0 b (Swap • iI) ((iI ↑) • Swap) _ _ Eq.refl
wn00125 : Base 3 → ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00125 b = win 0 3 b (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00126 : Base 3 → ⟪ (K0⁻ ∷ CK10⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
wn00126 b = win 3 0 b ((K • iI) • (S ↑ • CK₁₀) • K) ((S ↑ • CK₁₀)) _ _ Eq.refl
wn00127 : Base 3 → ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ ι1 ∷ []) ⟫ʷ
wn00127 b = win 3 0 b (iI • Swap) (Swap • (iI ↑)) _ _ Eq.refl
wn00128 : Base 3 → ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) ⟫ʷ
wn00128 b = win 0 3 b (Toff) (K • CCZ • (K • iI)) _ _ Eq.refl
wn00129 : Base 3 → ⟪ (Sw01 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00129 b = win 3 0 b (Swap • ((K • iI) ↑)) ((K • iI) • Swap) _ _ Eq.refl
wn00130 : Base 3 → ⟪ (Sw12 ∷ CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wn00130 b = win 0 3 b (Swap • (CS ↑) • Swap) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00131 : Base 3 → ⟪ (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
wn00131 b = win 3 0 b ((Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑)) ((CS • CS • CS)) _ _ Eq.refl
wn00132 : Base 3 → ⟪ (Sw12 ∷ CS02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wn00132 b = win 3 0 b ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) _ _ Eq.refl
wn00133 : Base 3 → ⟪ (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
wn00133 b = win 3 0 b ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00134 : Base 3 → ⟪ (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
wn00134 b = win 3 0 b ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00135 : Base 3 → ⟪ (Sw23 ∷ CS13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn00135 b = win 0 3 b ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) _ _ Eq.refl
wn00136 : Base 3 → ⟪ (Sw23 ∷ CX31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wn00136 b = win 0 3 b ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) _ _ Eq.refl
wn00137 : Base 3 → ⟪ (CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK21⁻ ∷ []) ⟫ʷ
wn00137 b = win 3 0 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn00138 : Base 3 → ⟪ (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
wn00138 b = win 0 3 b ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00139 : Base 3 → ⟪ (Sw01 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00139 b = win 3 0 b (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) _ _ Eq.refl
wn00140 : Base 3 → ⟪ (CK20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK21 ∷ []) ⟫ʷ
wn00140 b = win 3 0 b ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) _ _ Eq.refl
wn00141 : Base 3 → ⟪ (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
wn00141 b = win 0 3 b ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00142 : Base 3 → ⟪ (Sw01 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw01 ∷ []) ⟫ʷ
wn00142 b = win 3 0 b (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00143 : Base 3 → ⟪ (Sw12 ∷ CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn00143 b = win 3 0 b ((Swap ↑) • (CS ↑) • (Swap ↑)) ((CS ↑)) _ _ Eq.refl
wn00144 : Base 3 → ⟪ (Sw12 ∷ CX20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wn00144 b = win 3 0 b ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) _ _ Eq.refl
wn00145 : Base 3 → ⟪ (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn00145 b = win 3 0 b ((Swap ↑) • (CS • CS • CS) • (Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00146 : Base 3 → ⟪ (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wn00146 b = win 3 0 b ((Swap ↑) • CS • (Swap ↑)) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00147 : Base 3 → ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00147 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) (CCZ) _ _ Eq.refl
wn00148 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn00148 b = win 3 0 b (ε) ((K • iI) • (S • S • S) • K • (K • iI) • S • K) _ _ Eq.refl
wn00149 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00149 b = win 3 0 b ((K • iI) • S • K • Toff • (K • iI) • (S • S • S) • K) (Toff) _ _ Eq.refl
wn00150 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ CX20 ∷ S2 ∷ []) ⟫ʷ
wn00150 b = win 3 0 b ((K • iI) • S • K • (Swap ↑ • CS • Swap ↑) • (K • iI) • (S • S • S) • K) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00151 : Base 3 → ⟪ (Sw23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ Sw23 ∷ []) ⟫ʷ
wn00151 b = win 0 3 b ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00152 : Base 3 → ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) ⟫ʷ
wn00152 b = win 3 0 b ((K • iI) • S • K • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (K • iI) • (S • S • S) • K) (((S • S • S) ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00153 : Base 3 → ⟪ (Sw23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00153 b = win 0 3 b ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00154 : Base 3 → ⟪ (S3 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00154 b = win 0 3 b ((S ↑ ↑) • ((S • S • S) ↑ ↑)) (ε) _ _ Eq.refl
wn00155 : Base 3 → ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ
wn00155 b = win 3 0 b (Toff) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) _ _ Eq.refl
wn00156 : Base 3 → ⟪ (CX31 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) ⟫ʷ
wn00156 b = win 0 3 b ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00157 : Base 3 → ⟪ (Sw12 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Sw12 ∷ []) ⟫ʷ
wn00157 b = win 0 3 b (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) _ _ Eq.refl
wn00158 : Base 3 → ⟪ (Sw12 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Sw12 ∷ []) ⟫ʷ
wn00158 b = win 0 3 b (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00159 : Base 3 → ⟪ (CX31 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) ⟫ʷ
wn00159 b = win 0 3 b ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀) ((S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00160 : Base 3 → ⟪ (CX20 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) ⟫ʷ
wn00160 b = win 3 0 b ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00161 : Base 3 → ⟪ (CX20 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00161 b = win 3 0 b ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) (ε) _ _ Eq.refl
wn00162 : Base 3 → ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00162 b = win 3 0 b ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) (Toff) _ _ Eq.refl
wn00163 : Base 3 → ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) ⟫ʷ
wn00163 b = win 0 3 b (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00164 : Base 3 → ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ
wn00164 b = win 3 0 b (CZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CZ) _ _ Eq.refl
wn00165 : Base 3 → ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ
wn00165 b = win 3 0 b (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) _ _ Eq.refl
wn00166 : Base 3 → ⟪ (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00166 b = win 0 3 b (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00167 : Base 3 → ⟪ (CZ01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CZ01 ∷ []) ⟫ʷ
wn00167 b = win 3 0 b (CZ • (CS ↑)) ((CS ↑) • CZ) _ _ Eq.refl
wn00168 : Base 3 → ⟪ (CZ01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CZ01 ∷ []) ⟫ʷ
wn00168 b = win 3 0 b (CZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CZ) _ _ Eq.refl
wn00169 : Base 3 → ⟪ (CS12 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00169 b = win 3 0 b ((CS ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • (CS ↑)) _ _ Eq.refl
wn00170 : Base 3 → ⟪ (CS12⁻ ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00170 b = win 3 0 b (((CS • CS • CS) ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00171 : Base 3 → ⟪ (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00171 b = win 3 0 b ((Swap ↑) • Toff • (Swap ↑)) (Toff) _ _ Eq.refl
wn00172 : Base 3 → ⟪ (CCZ012 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ012 ∷ []) ⟫ʷ
wn00172 b = win 3 0 b (CCZ • CZ) (CZ • CCZ) _ _ Eq.refl
wn00173 : Base 3 → ⟪ (X3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ X2 ∷ []) ⟫ʷ
wn00173 b = win 0 3 b ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) _ _ Eq.refl
wn00174 : Base 3 → ⟪ (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00174 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00175 : Base 3 → ⟪ (Sw23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Sw23 ∷ []) ⟫ʷ
wn00175 b = win 0 3 b ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00176 : Base 3 → ⟪ (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00176 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00177 : Base 3 → ⟪ (CCZ012 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00177 b = win 3 0 b (CCZ • (CS ↑)) ((CS ↑) • CCZ) _ _ Eq.refl
wn00178 : Base 3 → ⟪ (CCZ012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00178 b = win 3 0 b (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) _ _ Eq.refl
wn00179 : Base 3 → ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00179 b = win 0 3 b ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00180 : Base 3 → ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00180 b = win 3 0 b (CCZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00181 : Base 3 → ⟪ (CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00181 b = win 0 3 b ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00182 : Base 3 → ⟪ (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00182 b = win 3 0 b (Toff • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00183 : Base 3 → ⟪ (S0 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0 ∷ []) ⟫ʷ
wn00183 b = win 3 0 b (S • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • S) _ _ Eq.refl
wn00184 : Base 3 → ⟪ (S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0 ∷ []) ⟫ʷ
wn00184 b = win 3 0 b (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S) _ _ Eq.refl
wn00185 : Base 3 → ⟪ (S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0⁻ ∷ []) ⟫ʷ
wn00185 b = win 3 0 b ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00186 : Base 3 → ⟪ (S0⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn00186 b = win 3 0 b ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00187 : Base 3 → ⟪ (Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00187 b = win 3 0 b (Toff • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00188 : Base 3 → ⟪ (CCZ012 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ CCZ012 ∷ []) ⟫ʷ
wn00188 b = win 3 0 b (CCZ • Z) (Z • CCZ) _ _ Eq.refl
wn00189 : Base 3 → ⟪ (CZ02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ []) ⟫ʷ
wn00189 b = win 3 0 b ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) _ _ Eq.refl
wn00190 : Base 3 → ⟪ (CS13 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS13 ∷ []) ⟫ʷ
wn00190 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • CZ) (CZ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00191 : Base 3 → ⟪ (Sw01 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw01 ∷ []) ⟫ʷ
wn00191 b = win 3 0 b (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) _ _ Eq.refl
wn00192 : Base 3 → ⟪ (CS01⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00192 b = win 3 0 b ((CS • CS • CS) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00193 : Base 3 → ⟪ (CS01 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS01 ∷ []) ⟫ʷ
wn00193 b = win 3 0 b (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) _ _ Eq.refl
wn00194 : Base 3 → ⟪ (CS02 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00194 b = win 3 0 b ((Swap ↑ • CS • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00195 : Base 3 → ⟪ (CS02⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00195 b = win 3 0 b ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00196 : Base 3 → ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00196 b = win 3 0 b ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00197 : Base 3 → ⟪ (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00197 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00198 : Base 3 → ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00198 b = win 0 3 b ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00199 : Base 3 → ⟪ (CS01⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn00199 b = win 3 0 b ((CS • CS • CS) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00200 : Base 3 → ⟪ (CS01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS01 ∷ []) ⟫ʷ
wn00200 b = win 3 0 b (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) _ _ Eq.refl
wn00201 : Base 3 → ⟪ (Toff102 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff102 ∷ []) ⟫ʷ
wn00201 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • S) (S • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00202 : Base 3 → ⟪ (Toff102 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff102 ∷ []) ⟫ʷ
wn00202 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • (S • S • S)) ((S • S • S) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00203 : Base 3 → ⟪ (CS12 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12 ∷ []) ⟫ʷ
wn00203 b = win 3 0 b ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
wn00204 : Base 3 → ⟪ (CS12 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00204 b = win 3 0 b ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00205 : Base 3 → ⟪ (CS12 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS12 ∷ []) ⟫ʷ
wn00205 b = win 3 0 b ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00206 : Base 3 → ⟪ (CS12⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00206 b = win 3 0 b (((CS • CS • CS) ↑) • S) (S • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00207 : Base 3 → ⟪ (CS12⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00207 b = win 3 0 b (((CS • CS • CS) ↑) • (S • S • S)) ((S • S • S) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00208 : Base 3 → ⟪ (CS12⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00208 b = win 3 0 b (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00209 : Base 3 → ⟪ (Toff102 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00209 b = win 3 0 b ((K ↑ • CCZ • K ↑ • iI) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00210 : Base 3 → ⟪ (S2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2 ∷ []) ⟫ʷ
wn00210 b = win 0 3 b ((S ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00211 : Base 3 → ⟪ (S2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2 ∷ []) ⟫ʷ
wn00211 b = win 0 3 b ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00212 : Base 3 → ⟪ (S2⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2⁻ ∷ []) ⟫ʷ
wn00212 b = win 0 3 b (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00213 : Base 3 → ⟪ (S2⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ
wn00213 b = win 0 3 b (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00214 : Base 3 → ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00214 b = win 3 0 b (CCZ • (S • S • S)) ((S • S • S) • CCZ) _ _ Eq.refl
wn00215 : Base 3 → ⟪ (X2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ X1 ∷ []) ⟫ʷ
wn00215 b = win 3 0 b ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) _ _ Eq.refl
