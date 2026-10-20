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
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn00001 : ⟪ [] ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ
wn00001 = win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00002 : ⟪ [] ⟫ʷ ≈ ⟪ (CX20 ∷ CX20 ∷ []) ⟫ʷ
wn00002 = win 3 0 complete₃ (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00003 : ⟪ (Sw23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00003 = win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) _ _ Eq.refl
wn00004 : ⟪ [] ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ
wn00004 = win 3 0 complete₃ (ε) (CCZ • CCZ) _ _ Eq.refl
wn00005 : ⟪ [] ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ
wn00005 = win 3 0 complete₃ (ε) (Swap • Swap) _ _ Eq.refl
wn00006 : ⟪ (CX20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ []) ⟫ʷ
wn00006 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) _ _ Eq.refl
wn00007 : ⟪ (CS02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12 ∷ []) ⟫ʷ
wn00007 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) _ _ Eq.refl
wn00008 : ⟪ (CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX10 ∷ []) ⟫ʷ
wn00008 = win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) _ _ Eq.refl
wn00009 : ⟪ (CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00009 = win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00010 : ⟪ (CS12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS02 ∷ []) ⟫ʷ
wn00010 = win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00011 : ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00011 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00012 : ⟪ [] ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ
wn00012 = win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00013 : ⟪ (CX31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX32 ∷ []) ⟫ʷ
wn00013 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) _ _ Eq.refl
wn00014 : ⟪ (Sw12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00014 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) _ _ Eq.refl
wn00015 : ⟪ (CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00015 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00016 : ⟪ (CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS12 ∷ []) ⟫ʷ
wn00016 = win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00017 : ⟪ (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00017 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00018 : ⟪ (Sw12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw12 ∷ []) ⟫ʷ
wn00018 = win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) _ _ Eq.refl
wn00019 : ⟪ (Sw12 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00019 = win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) _ _ Eq.refl
wn00020 : ⟪ (Sw12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw12 ∷ []) ⟫ʷ
wn00020 = win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) _ _ Eq.refl
wn00021 : ⟪ (Sw12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00021 = win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) _ _ Eq.refl
wn00022 : ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
wn00022 = win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) _ _ Eq.refl
wn00023 : ⟪ (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ
wn00023 = win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) _ _ Eq.refl
wn00024 : ⟪ (Sw01 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Sw01 ∷ []) ⟫ʷ
wn00024 = win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) _ _ Eq.refl
wn00025 : ⟪ (Sw01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw01 ∷ []) ⟫ʷ
wn00025 = win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) _ _ Eq.refl
wn00026 : ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00026 = win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00027 : ⟪ (Sw01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw01 ∷ []) ⟫ʷ
wn00027 = win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) _ _ Eq.refl
wn00028 : ⟪ (Sw01 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sw01 ∷ []) ⟫ʷ
wn00028 = win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) _ _ Eq.refl
wn00029 : ⟪ (Sw01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00029 = win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) _ _ Eq.refl
wn00030 : ⟪ (Sw01 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Sw01 ∷ []) ⟫ʷ
wn00030 = win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00031 : ⟪ (Sw01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00031 = win 3 0 complete₃ (Swap • Swap) (ε) _ _ Eq.refl
wn00032 : ⟪ (CCZ012 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00032 = win 3 0 complete₃ (CCZ • CCZ) (ε) _ _ Eq.refl
wn00033 : ⟪ (CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00033 = win 0 3 complete₃ (CCZ • CCZ) (ε) _ _ Eq.refl
wn00034 : ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00034 = win 0 3 complete₃ (CCZ) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00035 : ⟪ (CS12 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CS12 ∷ []) ⟫ʷ
wn00035 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00036 : ⟪ (CX13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX23 ∷ []) ⟫ʷ
wn00036 = win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) _ _ Eq.refl
wn00037 : ⟪ (CX23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX13 ∷ []) ⟫ʷ
wn00037 = win 0 3 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00038 : ⟪ (CS23⁻ ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00038 = win 0 3 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00039 : ⟪ (Sw01 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sw01 ∷ []) ⟫ʷ
wn00039 = win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00040 : ⟪ (CS23 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS23 ∷ []) ⟫ʷ
wn00040 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00041 : ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00041 = win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00042 : ⟪ [] ⟫ʷ ≈ ⟪ (CX23 ∷ CX23 ∷ []) ⟫ʷ
wn00042 = win 0 3 complete₃ (ε) ((CX₀₁ ↑) • (CX₀₁ ↑)) _ _ Eq.refl
wn00043 : ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ⟫ʷ
wn00043 = win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00044 : ⟪ (CX23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX32 ∷ []) ⟫ʷ
wn00044 = win 0 3 complete₃ ((CX₀₁ ↑) • (Swap ↑)) ((Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00045 : ⟪ [] ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff012 ∷ []) ⟫ʷ
wn00045 = win 3 0 complete₃ (ε) (Toff • Toff) _ _ Eq.refl
wn00046 : ⟪ (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00046 = win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00047 : ⟪ (CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13⁻ ∷ []) ⟫ʷ
wn00047 = win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00048 : ⟪ (CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS13 ∷ []) ⟫ʷ
wn00048 = win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00049 : ⟪ (Sw12 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw12 ∷ []) ⟫ʷ
wn00049 = win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) _ _ Eq.refl
wn00050 : ⟪ (Sw12 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ Sw12 ∷ []) ⟫ʷ
wn00050 = win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00051 : ⟪ (Sw12 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ
wn00051 = win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) _ _ Eq.refl
wn00052 : ⟪ (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00052 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00053 : ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ
wn00053 = win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) _ _ Eq.refl
wn00054 : ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0 ∷ []) ⟫ʷ
wn00054 = win 3 0 complete₃ (ε) ((K • iI) • K) _ _ Eq.refl
wn00055 : ⟪ (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00055 = win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) _ _ Eq.refl
wn00056 : ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ⟫ʷ
wn00056 = win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00057 : ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ
wn00057 = win 3 0 complete₃ (Toff) (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI)) _ _ Eq.refl
wn00058 : ⟪ (CX23 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CX23 ∷ []) ⟫ʷ
wn00058 = win 0 3 complete₃ ((CX₀₁ ↑) • CX₁₀) (CX₁₀ • (CX₀₁ ↑)) _ _ Eq.refl
wn00059 : ⟪ (CX23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX23 ∷ []) ⟫ʷ
wn00059 = win 0 3 complete₃ ((CX₀₁ ↑) • CS) (CS • (CX₀₁ ↑)) _ _ Eq.refl
wn00060 : ⟪ (CX23 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00060 = win 0 3 complete₃ ((CX₀₁ ↑) • (CX₀₁ ↑)) (ε) _ _ Eq.refl
wn00061 : ⟪ (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00061 = win 3 0 complete₃ (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI)) (Toff) _ _ Eq.refl
wn00062 : ⟪ (Sw23 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Sw23 ∷ []) ⟫ʷ
wn00062 = win 0 3 complete₃ ((Swap ↑) • CX₁₀) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00063 : ⟪ (Sw23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw23 ∷ []) ⟫ʷ
wn00063 = win 0 3 complete₃ ((Swap ↑) • CS) ((Swap ↑ • CS • Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00064 : ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) ⟫ʷ
wn00064 = win 3 0 complete₃ (Toff) (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) _ _ Eq.refl
wn00065 : ⟪ (CS13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23 ∷ []) ⟫ʷ
wn00065 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) _ _ Eq.refl
wn00066 : ⟪ (CS13 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00066 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00067 : ⟪ (CS12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS12 ∷ []) ⟫ʷ
wn00067 = win 3 0 complete₃ ((CS ↑) • CS) (CS • (CS ↑)) _ _ Eq.refl
wn00068 : ⟪ (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00068 = win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) (Toff) _ _ Eq.refl
wn00069 : ⟪ [] ⟫ʷ ≈ ⟪ (CX10 ∷ CX10 ∷ []) ⟫ʷ
wn00069 = win 3 0 complete₃ (ε) (CX₁₀ • CX₁₀) _ _ Eq.refl
wn00070 : ⟪ [] ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ123 ∷ []) ⟫ʷ
wn00070 = win 0 3 complete₃ (ε) (CCZ • CCZ) _ _ Eq.refl
wn00071 : ⟪ (Sw23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw23 ∷ []) ⟫ʷ
wn00071 = win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) _ _ Eq.refl
wn00072 : ⟪ (Sw23 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00072 = win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) _ _ Eq.refl
wn00073 : ⟪ (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ⟫ʷ
wn00073 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00074 : ⟪ (CX02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ []) ⟫ʷ
wn00074 = win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) _ _ Eq.refl
wn00075 : ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) ⟫ʷ
wn00075 = win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00076 : ⟪ (CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00076 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00077 : ⟪ (CS23 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00077 = win 0 3 complete₃ ((CS ↑) • (CS • CS • CS)) ((CS • CS • CS) • (CS ↑)) _ _ Eq.refl
wn00078 : ⟪ (CX32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CX31 ∷ []) ⟫ʷ
wn00078 = win 0 3 complete₃ ((CX₁₀ ↑) • Swap) (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00079 : ⟪ (CS12⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00079 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00080 : ⟪ (CS12 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00080 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00081 : ⟪ (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00081 = win 0 3 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) _ _ Eq.refl
wn00082 : ⟪ (CS23 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS23 ∷ []) ⟫ʷ
wn00082 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00083 : ⟪ (CX21 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CX21 ∷ []) ⟫ʷ
wn00083 = win 3 0 complete₃ ((CX₁₀ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00084 : ⟪ (CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CS23⁻ ∷ []) ⟫ʷ
wn00084 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00085 : ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ
wn00085 = win 3 0 complete₃ (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00086 : ⟪ (CS12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00086 = win 0 3 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) _ _ Eq.refl
wn00087 : ⟪ (CS01⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn00087 = win 3 0 complete₃ ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00088 : ⟪ (CS01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS01 ∷ []) ⟫ʷ
wn00088 = win 3 0 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) _ _ Eq.refl
wn00089 : ⟪ (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00089 = win 3 0 complete₃ (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00090 : ⟪ (CS12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12 ∷ []) ⟫ʷ
wn00090 = win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) _ _ Eq.refl
wn00091 : ⟪ (CS23 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS23 ∷ []) ⟫ʷ
wn00091 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00092 : ⟪ (CX21 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CX21 ∷ []) ⟫ʷ
wn00092 = win 3 0 complete₃ ((CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00093 : ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ
wn00093 = win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CS) _ _ Eq.refl
wn00094 : ⟪ (CS01⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00094 = win 3 0 complete₃ ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00095 : ⟪ (CS01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS01 ∷ []) ⟫ʷ
wn00095 = win 3 0 complete₃ (CS • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CS) _ _ Eq.refl
wn00096 : ⟪ (CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ23 ∷ []) ⟫ʷ
wn00096 = win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) _ _ Eq.refl
wn00097 : ⟪ (CZ23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CZ13 ∷ []) ⟫ʷ
wn00097 = win 0 3 complete₃ ((CZ ↑) • Swap) (Swap • (Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn00098 : ⟪ (CZ13 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CZ13 ∷ []) ⟫ʷ
wn00098 = win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn00099 : ⟪ (CZ12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CZ12 ∷ []) ⟫ʷ
wn00099 = win 3 0 complete₃ ((CZ ↑) • CS) (CS • (CZ ↑)) _ _ Eq.refl
wn00100 : ⟪ (CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) ⟫ʷ
wn00100 = win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00101 : ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ
wn00101 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00102 : ⟪ (CS01⁻ ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00102 = win 3 0 complete₃ ((CS • CS • CS) • (CS ↑)) ((CS ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00103 : ⟪ (CS01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS01 ∷ []) ⟫ʷ
wn00103 = win 3 0 complete₃ (CS • (CS ↑)) ((CS ↑) • CS) _ _ Eq.refl
wn00104 : ⟪ (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00104 = win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) _ _ Eq.refl
wn00105 : ⟪ [] ⟫ʷ ≈ ⟪ (CX32 ∷ CX32 ∷ []) ⟫ʷ
wn00105 = win 0 3 complete₃ (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00106 : ⟪ (CS12 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS12 ∷ []) ⟫ʷ
wn00106 = win 0 3 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) _ _ Eq.refl
wn00107 : ⟪ (Sw12 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw12 ∷ []) ⟫ʷ
wn00107 = win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) _ _ Eq.refl
wn00108 : ⟪ (Sw12 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Sw12 ∷ []) ⟫ʷ
wn00108 = win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) _ _ Eq.refl
wn00109 : ⟪ (CS01⁻ ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00109 = win 3 0 complete₃ ((CS • CS • CS) • (CZ ↑)) ((CZ ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00110 : ⟪ (CS01 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS01 ∷ []) ⟫ʷ
wn00110 = win 3 0 complete₃ (CS • (CZ ↑)) ((CZ ↑) • CS) _ _ Eq.refl
wn00111 : ⟪ [] ⟫ʷ ≈ ⟪ (CX31 ∷ CX31 ∷ []) ⟫ʷ
wn00111 = win 0 3 complete₃ (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00112 : ⟪ (CX20 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CX20 ∷ []) ⟫ʷ
wn00112 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CX₁₀ ↑)) ((CX₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00113 : ⟪ (Sw12 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw12 ∷ []) ⟫ʷ
wn00113 = win 0 3 complete₃ (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) _ _ Eq.refl
wn00114 : ⟪ (Sw12 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Sw12 ∷ []) ⟫ʷ
wn00114 = win 0 3 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00115 : ⟪ [] ⟫ʷ ≈ ⟪ (CX13 ∷ CX13 ∷ []) ⟫ʷ
wn00115 = win 0 3 complete₃ (ε) ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00116 : ⟪ [] ⟫ʷ ≈ ⟪ (K0 ∷ K0⁻ ∷ []) ⟫ʷ
wn00116 = win 3 0 complete₃ (ε) (K • (K • iI)) _ _ Eq.refl
wn00117 : ⟪ (K0⁻ ∷ CK10 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
wn00117 = win 3 0 complete₃ ((K • iI) • CK₁₀ • K) (CK₁₀) _ _ Eq.refl
wn00118 : ⟪ (K0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1 ∷ []) ⟫ʷ
wn00118 = win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) _ _ Eq.refl
wn00119 : ⟪ (K0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ K1⁻ ∷ []) ⟫ʷ
wn00119 = win 3 0 complete₃ ((K • iI) • Swap) (Swap • ((K • iI) ↑)) _ _ Eq.refl
wn00120 : ⟪ (K1⁻ ∷ CCZ123 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ []) ⟫ʷ
wn00120 = win 0 3 complete₃ ((K • iI) • CCZ • K) (Toff) _ _ Eq.refl
wn00121 : ⟪ (Sw01 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sw01 ∷ []) ⟫ʷ
wn00121 = win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) _ _ Eq.refl
wn00122 : ⟪ (Sw01 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ
wn00122 = win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) _ _ Eq.refl
wn00123 : ⟪ (Sw01 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sw01 ∷ []) ⟫ʷ
wn00123 = win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) _ _ Eq.refl
wn00124 : ⟪ (Sw01 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι1 ∷ Sw01 ∷ []) ⟫ʷ
wn00124 = win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) _ _ Eq.refl
wn00125 : ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ⟫ʷ
wn00125 = win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00126 : ⟪ (K0⁻ ∷ CK10⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
wn00126 = win 3 0 complete₃ ((K • iI) • (S ↑ • CK₁₀) • K) ((S ↑ • CK₁₀)) _ _ Eq.refl
wn00127 : ⟪ (ι ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ ι1 ∷ []) ⟫ʷ
wn00127 = win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) _ _ Eq.refl
wn00128 : ⟪ (Toff123 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) ⟫ʷ
wn00128 = win 0 3 complete₃ (Toff) (K • CCZ • (K • iI)) _ _ Eq.refl
wn00129 : ⟪ (Sw01 ∷ K1⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00129 = win 3 0 complete₃ (Swap • ((K • iI) ↑)) ((K • iI) • Swap) _ _ Eq.refl
wn00130 : ⟪ (Sw12 ∷ CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
wn00130 = win 0 3 complete₃ (Swap • (CS ↑) • Swap) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00131 : ⟪ (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
wn00131 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑)) ((CS • CS • CS)) _ _ Eq.refl
wn00132 : ⟪ (Sw12 ∷ CS02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
wn00132 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) _ _ Eq.refl
wn00133 : ⟪ (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
wn00133 = win 3 0 complete₃ ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00134 : ⟪ (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
wn00134 = win 3 0 complete₃ ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00135 : ⟪ (Sw23 ∷ CS13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn00135 = win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) _ _ Eq.refl
wn00136 : ⟪ (Sw23 ∷ CX31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wn00136 = win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) _ _ Eq.refl
wn00137 : ⟪ (CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK21⁻ ∷ []) ⟫ʷ
wn00137 = win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn00138 : ⟪ (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
wn00138 = win 0 3 complete₃ ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00139 : ⟪ (Sw01 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ
wn00139 = win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) _ _ Eq.refl
wn00140 : ⟪ (CK20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK21 ∷ []) ⟫ʷ
wn00140 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) _ _ Eq.refl
wn00141 : ⟪ (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
wn00141 = win 0 3 complete₃ ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00142 : ⟪ (Sw01 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw01 ∷ []) ⟫ʷ
wn00142 = win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00143 : ⟪ (Sw12 ∷ CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
wn00143 = win 3 0 complete₃ ((Swap ↑) • (CS ↑) • (Swap ↑)) ((CS ↑)) _ _ Eq.refl
wn00144 : ⟪ (Sw12 ∷ CX20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
wn00144 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) _ _ Eq.refl
wn00145 : ⟪ (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
wn00145 = win 3 0 complete₃ ((Swap ↑) • (CS • CS • CS) • (Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00146 : ⟪ (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
wn00146 = win 3 0 complete₃ ((Swap ↑) • CS • (Swap ↑)) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00147 : ⟪ (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
wn00147 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) (CCZ) _ _ Eq.refl
wn00148 : ⟪ [] ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
wn00148 = win 3 0 complete₃ (ε) ((K • iI) • (S • S • S) • K • (K • iI) • S • K) _ _ Eq.refl
wn00149 : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00149 = win 3 0 complete₃ ((K • iI) • S • K • Toff • (K • iI) • (S • S • S) • K) (Toff) _ _ Eq.refl
wn00150 : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ CX20 ∷ S2 ∷ []) ⟫ʷ
wn00150 = win 3 0 complete₃ ((K • iI) • S • K • (Swap ↑ • CS • Swap ↑) • (K • iI) • (S • S • S) • K) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00151 : ⟪ (Sw23 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ Sw23 ∷ []) ⟫ʷ
wn00151 = win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00152 : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) ⟫ʷ
wn00152 = win 3 0 complete₃ ((K • iI) • S • K • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (K • iI) • (S • S • S) • K) (((S • S • S) ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00153 : ⟪ (Sw23 ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Sw23 ∷ []) ⟫ʷ
wn00153 = win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00154 : ⟪ (S3 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00154 = win 0 3 complete₃ ((S ↑ ↑) • ((S • S • S) ↑ ↑)) (ε) _ _ Eq.refl
wn00155 : ⟪ (Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ
wn00155 = win 3 0 complete₃ (Toff) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) _ _ Eq.refl
wn00156 : ⟪ (CX31 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) ⟫ʷ
wn00156 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00157 : ⟪ (Sw12 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Sw12 ∷ []) ⟫ʷ
wn00157 = win 0 3 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) _ _ Eq.refl
wn00158 : ⟪ (Sw12 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Sw12 ∷ []) ⟫ʷ
wn00158 = win 0 3 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00159 : ⟪ (CX31 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) ⟫ʷ
wn00159 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀) ((S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00160 : ⟪ (CX20 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) ⟫ʷ
wn00160 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00161 : ⟪ (CX20 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00161 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) (ε) _ _ Eq.refl
wn00162 : ⟪ (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00162 = win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) (Toff) _ _ Eq.refl
wn00163 : ⟪ (CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) ⟫ʷ
wn00163 = win 0 3 complete₃ (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00164 : ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ
wn00164 = win 3 0 complete₃ (CZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CZ) _ _ Eq.refl
wn00165 : ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ
wn00165 = win 3 0 complete₃ (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) _ _ Eq.refl
wn00166 : ⟪ (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
wn00166 = win 0 3 complete₃ (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00167 : ⟪ (CZ01 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CZ01 ∷ []) ⟫ʷ
wn00167 = win 3 0 complete₃ (CZ • (CS ↑)) ((CS ↑) • CZ) _ _ Eq.refl
wn00168 : ⟪ (CZ01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CZ01 ∷ []) ⟫ʷ
wn00168 = win 3 0 complete₃ (CZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CZ) _ _ Eq.refl
wn00169 : ⟪ (CS12 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00169 = win 3 0 complete₃ ((CS ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • (CS ↑)) _ _ Eq.refl
wn00170 : ⟪ (CS12⁻ ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00170 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00171 : ⟪ (Sw12 ∷ Toff012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
wn00171 = win 3 0 complete₃ ((Swap ↑) • Toff • (Swap ↑)) (Toff) _ _ Eq.refl
wn00172 : ⟪ (CCZ012 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ012 ∷ []) ⟫ʷ
wn00172 = win 3 0 complete₃ (CCZ • CZ) (CZ • CCZ) _ _ Eq.refl
wn00173 : ⟪ (X3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ X2 ∷ []) ⟫ʷ
wn00173 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) _ _ Eq.refl
wn00174 : ⟪ (CS02 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00174 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00175 : ⟪ (Sw23 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Sw23 ∷ []) ⟫ʷ
wn00175 = win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00176 : ⟪ (CS02⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00176 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00177 : ⟪ (CCZ012 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00177 = win 3 0 complete₃ (CCZ • (CS ↑)) ((CS ↑) • CCZ) _ _ Eq.refl
wn00178 : ⟪ (CCZ012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ012 ∷ []) ⟫ʷ
wn00178 = win 3 0 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) _ _ Eq.refl
wn00179 : ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00179 = win 0 3 complete₃ ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00180 : ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00180 = win 3 0 complete₃ (CCZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00181 : ⟪ (CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00181 = win 0 3 complete₃ ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00182 : ⟪ (Toff012 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00182 = win 3 0 complete₃ (Toff • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00183 : ⟪ (S0 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0 ∷ []) ⟫ʷ
wn00183 = win 3 0 complete₃ (S • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • S) _ _ Eq.refl
wn00184 : ⟪ (S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0 ∷ []) ⟫ʷ
wn00184 = win 3 0 complete₃ (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S) _ _ Eq.refl
wn00185 : ⟪ (S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0⁻ ∷ []) ⟫ʷ
wn00185 = win 3 0 complete₃ ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00186 : ⟪ (S0⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0⁻ ∷ []) ⟫ʷ
wn00186 = win 3 0 complete₃ ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00187 : ⟪ (Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
wn00187 = win 3 0 complete₃ (Toff • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00188 : ⟪ (CCZ012 ∷ Z0 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ CCZ012 ∷ []) ⟫ʷ
wn00188 = win 3 0 complete₃ (CCZ • Z) (Z • CCZ) _ _ Eq.refl
wn00189 : ⟪ (CZ02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ []) ⟫ʷ
wn00189 = win 3 0 complete₃ ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) _ _ Eq.refl
wn00190 : ⟪ (CS13 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS13 ∷ []) ⟫ʷ
wn00190 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CZ) (CZ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00191 : ⟪ (Sw01 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw01 ∷ []) ⟫ʷ
wn00191 = win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) _ _ Eq.refl
wn00192 : ⟪ (CS01⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS01⁻ ∷ []) ⟫ʷ
wn00192 = win 3 0 complete₃ ((CS • CS • CS) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00193 : ⟪ (CS01 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS01 ∷ []) ⟫ʷ
wn00193 = win 3 0 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) _ _ Eq.refl
wn00194 : ⟪ (CS02 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ []) ⟫ʷ
wn00194 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00195 : ⟪ (CS02⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ []) ⟫ʷ
wn00195 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00196 : ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ⟫ʷ
wn00196 = win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00197 : ⟪ (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00197 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00198 : ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ
wn00198 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00199 : ⟪ (CS01⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
wn00199 = win 3 0 complete₃ ((CS • CS • CS) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00200 : ⟪ (CS01 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CS01 ∷ []) ⟫ʷ
wn00200 = win 3 0 complete₃ (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) _ _ Eq.refl
wn00201 : ⟪ (Toff102 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff102 ∷ []) ⟫ʷ
wn00201 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • S) (S • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00202 : ⟪ (Toff102 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ Toff102 ∷ []) ⟫ʷ
wn00202 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (S • S • S)) ((S • S • S) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00203 : ⟪ (CS12 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12 ∷ []) ⟫ʷ
wn00203 = win 3 0 complete₃ ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
wn00204 : ⟪ (CS12 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12 ∷ []) ⟫ʷ
wn00204 = win 3 0 complete₃ ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00205 : ⟪ (CS12 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS12 ∷ []) ⟫ʷ
wn00205 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00206 : ⟪ (CS12⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00206 = win 3 0 complete₃ (((CS • CS • CS) ↑) • S) (S • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00207 : ⟪ (CS12⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
wn00207 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (S • S • S)) ((S • S • S) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00208 : ⟪ (CS12⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS12⁻ ∷ []) ⟫ʷ
wn00208 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00209 : ⟪ (Toff102 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
wn00209 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00210 : ⟪ (S2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2 ∷ []) ⟫ʷ
wn00210 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00211 : ⟪ (S2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2 ∷ []) ⟫ʷ
wn00211 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00212 : ⟪ (S2⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S2⁻ ∷ []) ⟫ʷ
wn00212 = win 0 3 complete₃ (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00213 : ⟪ (S2⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ
wn00213 = win 0 3 complete₃ (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00214 : ⟪ (CCZ012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CCZ012 ∷ []) ⟫ʷ
wn00214 = win 3 0 complete₃ (CCZ • (S • S • S)) ((S • S • S) • CCZ) _ _ Eq.refl
wn00215 : ⟪ (X2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ X1 ∷ []) ⟫ʷ
wn00215 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) _ _ Eq.refl
