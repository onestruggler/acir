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

module Examples.Groups.Clifford+CS.Four.Wins.W01 where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)

wn00001 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((Swap ↑) • (Swap ↑))
wn00001 = win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00002 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑))
wn00002 = win 3 0 complete₃ (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00003 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (Swap ↑)) ≈ insʷ 0 (ε)
wn00003 = win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) _ _ Eq.refl
wn00004 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (CCZ • CCZ)
wn00004 = win 3 0 complete₃ (ε) (CCZ • CCZ) _ _ Eq.refl
wn00005 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (Swap • Swap)
wn00005 = win 3 0 complete₃ (ε) (Swap • Swap) _ _ Eq.refl
wn00006 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) ≈ insʷ 3 (Swap • (CX₁₀ ↑))
wn00006 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) _ _ Eq.refl
wn00007 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • Swap) ≈ insʷ 3 (Swap • (CS ↑))
wn00007 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) _ _ Eq.refl
wn00008 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CX₀₁ • Swap) ≈ insʷ 3 (Swap • CX₁₀)
wn00008 = win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) _ _ Eq.refl
wn00009 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • Swap) ≈ insʷ 3 (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00009 = win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00010 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • Swap) ≈ insʷ 3 (Swap • (Swap ↑ • CS • Swap ↑))
wn00010 = win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00011 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ≈ insʷ 3 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00011 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00012 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((Swap ↑) • (Swap ↑))
wn00012 = win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00013 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) ≈ insʷ 0 (Swap • (CX₁₀ ↑))
wn00013 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) _ _ Eq.refl
wn00014 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (Swap ↑)) ≈ insʷ 3 (ε)
wn00014 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) _ _ Eq.refl
wn00015 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • ((CS • CS • CS) ↑))
wn00015 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00016 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (CS ↑))
wn00016 = win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00017 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ≈ insʷ 3 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00017 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00018 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CS ↑)) ≈ insʷ 3 ((CS ↑) • (Swap ↑))
wn00018 = win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) _ _ Eq.refl
wn00019 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • (Swap ↑))
wn00019 = win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) _ _ Eq.refl
wn00020 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((CS ↑) • Swap)
wn00020 = win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) _ _ Eq.refl
wn00021 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • Swap)
wn00021 = win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) _ _ Eq.refl
wn00022 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑) • Swap) ≈ insʷ 0 ((Swap ↑) • Swap • (Swap ↑))
wn00022 = win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) _ _ Eq.refl
wn00023 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • Swap • (Swap ↑)) ≈ insʷ 0 (Swap • (Swap ↑) • Swap)
wn00023 = win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) _ _ Eq.refl
wn00024 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ≈ insʷ 3 ((CX₀₁ ↑) • Swap)
wn00024 = win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) _ _ Eq.refl
wn00025 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((CS ↑) • Swap)
wn00025 = win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) _ _ Eq.refl
wn00026 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00026 = win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00027 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (CS ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • Swap)
wn00027 = win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) _ _ Eq.refl
wn00028 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • CX₀₁) ≈ insʷ 3 (CX₁₀ • Swap)
wn00028 = win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) _ _ Eq.refl
wn00029 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • ((CS • CS • CS) ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap)
wn00029 = win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) _ _ Eq.refl
wn00030 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (CX₀₁ ↑)) ≈ insʷ 3 ((Swap ↑ • CX₀₁ • Swap ↑) • Swap)
wn00030 = win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00031 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • Swap) ≈ insʷ 3 (ε)
wn00031 = win 3 0 complete₃ (Swap • Swap) (ε) _ _ Eq.refl
wn00032 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • CCZ) ≈ insʷ 3 (ε)
wn00032 = win 3 0 complete₃ (CCZ • CCZ) (ε) _ _ Eq.refl
wn00033 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ • CCZ) ≈ insʷ 0 (ε)
wn00033 = win 0 3 complete₃ (CCZ • CCZ) (ε) _ _ Eq.refl
wn00034 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ) ≈ insʷ 0 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00034 = win 0 3 complete₃ (CCZ) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00035 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑))
wn00035 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00036 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) ≈ insʷ 0 (Swap • (CX₀₁ ↑))
wn00036 = win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) _ _ Eq.refl
wn00037 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₀₁ ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑ • CX₀₁ • Swap ↑))
wn00037 = win 0 3 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00038 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑))
wn00038 = win 0 3 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00039 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (CX₁₀ ↑)) ≈ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • Swap)
wn00039 = win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00040 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑))
wn00040 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00041 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 (CCZ)
wn00041 = win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00042 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((CX₀₁ ↑) • (CX₀₁ ↑))
wn00042 = win 0 3 complete₃ (ε) ((CX₀₁ ↑) • (CX₀₁ ↑)) _ _ Eq.refl
wn00043 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00043 = win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00044 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₀₁ ↑) • (Swap ↑)) ≈ insʷ 0 ((Swap ↑) • (CX₁₀ ↑))
wn00044 = win 0 3 complete₃ ((CX₀₁ ↑) • (Swap ↑)) ((Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00045 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (Toff • Toff)
wn00045 = win 3 0 complete₃ (ε) (Toff • Toff) _ _ Eq.refl
wn00046 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) ≈ insʷ 3 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI)
wn00046 = win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00047 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((CS • CS • CS) ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00047 = win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00048 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑ • CS • Swap ↑))
wn00048 = win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00049 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (CS ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • Swap)
wn00049 = win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) _ _ Eq.refl
wn00050 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CX₀₁ ↑)) ≈ insʷ 3 ((CX₁₀ ↑) • (Swap ↑))
wn00050 = win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) _ _ Eq.refl
wn00051 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • ((CS • CS • CS) ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap)
wn00051 = win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) _ _ Eq.refl
wn00052 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ≈ insʷ 0 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00052 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00053 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff) ≈ insʷ 3 (K • CCZ • (K • iI))
wn00053 = win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) _ _ Eq.refl
wn00054 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((K • iI) • K)
wn00054 = win 3 0 complete₃ (ε) ((K • iI) • K) _ _ Eq.refl
wn00055 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • CCZ • (K • iI)) ≈ insʷ 3 (Toff)
wn00055 = win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) _ _ Eq.refl
wn00056 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) ≈ insʷ 3 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI)
wn00056 = win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00057 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff) ≈ insʷ 3 (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI))
wn00057 = win 3 0 complete₃ (Toff) (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI)) _ _ Eq.refl
wn00058 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₀₁ ↑) • CX₁₀) ≈ insʷ 0 (CX₁₀ • (CX₀₁ ↑))
wn00058 = win 0 3 complete₃ ((CX₀₁ ↑) • CX₁₀) (CX₁₀ • (CX₀₁ ↑)) _ _ Eq.refl
wn00059 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₀₁ ↑) • CS) ≈ insʷ 0 (CS • (CX₀₁ ↑))
wn00059 = win 0 3 complete₃ ((CX₀₁ ↑) • CS) (CS • (CX₀₁ ↑)) _ _ Eq.refl
wn00060 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₀₁ ↑) • (CX₀₁ ↑)) ≈ insʷ 0 (ε)
wn00060 = win 0 3 complete₃ ((CX₀₁ ↑) • (CX₀₁ ↑)) (ε) _ _ Eq.refl
wn00061 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI)) ≈ insʷ 3 (Toff)
wn00061 = win 3 0 complete₃ (K • CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑) • (K • iI)) (Toff) _ _ Eq.refl
wn00062 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • CX₁₀) ≈ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑))
wn00062 = win 0 3 complete₃ ((Swap ↑) • CX₁₀) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00063 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • CS) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (Swap ↑))
wn00063 = win 0 3 complete₃ ((Swap ↑) • CS) ((Swap ↑ • CS • Swap ↑) • (Swap ↑)) _ _ Eq.refl
wn00064 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff) ≈ insʷ 3 (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI))
wn00064 = win 3 0 complete₃ (Toff) (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) _ _ Eq.refl
wn00065 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • Swap) ≈ insʷ 0 (Swap • (CS ↑))
wn00065 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) _ _ Eq.refl
wn00066 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • CX₀₁) ≈ insʷ 0 (CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00066 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00067 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • CS) ≈ insʷ 3 (CS • (CS ↑))
wn00067 = win 3 0 complete₃ ((CS ↑) • CS) (CS • (CS ↑)) _ _ Eq.refl
wn00068 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) ≈ insʷ 3 (Toff)
wn00068 = win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑) • CS • (K • iI)) (Toff) _ _ Eq.refl
wn00069 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (CX₁₀ • CX₁₀)
wn00069 = win 3 0 complete₃ (ε) (CX₁₀ • CX₁₀) _ _ Eq.refl
wn00070 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 (CCZ • CCZ)
wn00070 = win 0 3 complete₃ (ε) (CCZ • CCZ) _ _ Eq.refl
wn00071 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (CS ↑)) ≈ insʷ 0 ((CS ↑) • (Swap ↑))
wn00071 = win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) _ _ Eq.refl
wn00072 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • ((CS • CS • CS) ↑)) ≈ insʷ 0 (((CS • CS • CS) ↑) • (Swap ↑))
wn00072 = win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) _ _ Eq.refl
wn00073 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ≈ insʷ 0 ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑))
wn00073 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00074 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) ≈ insʷ 3 (Swap • (CX₀₁ ↑))
wn00074 = win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) _ _ Eq.refl
wn00075 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ) ≈ insʷ 0 (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑))
wn00075 = win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00076 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) ≈ insʷ 3 (Swap • ((CS • CS • CS) ↑))
wn00076 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00077 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (CS • CS • CS)) ≈ insʷ 0 ((CS • CS • CS) • (CS ↑))
wn00077 = win 0 3 complete₃ ((CS ↑) • (CS • CS • CS)) ((CS • CS • CS) • (CS ↑)) _ _ Eq.refl
wn00078 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CX₁₀ ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑ • CX₁₀ • Swap ↑))
wn00078 = win 0 3 complete₃ ((CX₁₀ ↑) • Swap) (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00079 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑))
wn00079 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00080 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑))
wn00080 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00081 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ≈ insʷ 0 (CCZ)
wn00081 = win 0 3 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) _ _ Eq.refl
wn00082 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑))
wn00082 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00083 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CX₁₀ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₁₀ ↑))
wn00083 = win 3 0 complete₃ ((CX₁₀ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00084 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) ≈ insʷ 0 (Swap • ((CS • CS • CS) ↑))
wn00084 = win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00085 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ) ≈ insʷ 3 (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑))
wn00085 = win 3 0 complete₃ (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00086 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS)
wn00086 = win 0 3 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) _ _ Eq.refl
wn00087 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS))
wn00087 = win 3 0 complete₃ ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00088 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS)
wn00088 = win 3 0 complete₃ (CS • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CS) _ _ Eq.refl
wn00089 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 (CCZ)
wn00089 = win 3 0 complete₃ (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00090 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • Toff) ≈ insʷ 3 (Toff • (CS ↑))
wn00090 = win 3 0 complete₃ ((CS ↑) • Toff) (Toff • (CS ↑)) _ _ Eq.refl
wn00091 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (CS ↑))
wn00091 = win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00092 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑))
wn00092 = win 3 0 complete₃ ((CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00093 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • CS)
wn00093 = win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CS) _ _ Eq.refl
wn00094 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS))
wn00094 = win 3 0 complete₃ ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00095 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CS)
wn00095 = win 3 0 complete₃ (CS • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CS) _ _ Eq.refl
wn00096 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CZ • Swap ↑) • Swap) ≈ insʷ 0 (Swap • (CZ ↑))
wn00096 = win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) _ _ Eq.refl
wn00097 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CZ ↑) • Swap) ≈ insʷ 0 (Swap • (Swap ↑ • CZ • Swap ↑))
wn00097 = win 0 3 complete₃ ((CZ ↑) • Swap) (Swap • (Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn00098 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CZ • Swap ↑) • CX₀₁) ≈ insʷ 0 (CX₀₁ • (Swap ↑ • CZ • Swap ↑))
wn00098 = win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • CX₀₁) (CX₀₁ • (Swap ↑ • CZ • Swap ↑)) _ _ Eq.refl
wn00099 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CZ ↑) • CS) ≈ insʷ 3 (CS • (CZ ↑))
wn00099 = win 3 0 complete₃ ((CZ ↑) • CS) (CS • (CZ ↑)) _ _ Eq.refl
wn00100 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ) ≈ insʷ 3 (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑))
wn00100 = win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00101 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • CS) ≈ insʷ 0 (CS • (Swap ↑ • CS • Swap ↑))
wn00101 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CS) (CS • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00102 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS • CS • CS) • (CS ↑)) ≈ insʷ 3 ((CS ↑) • (CS • CS • CS))
wn00102 = win 3 0 complete₃ ((CS • CS • CS) • (CS ↑)) ((CS ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00103 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • (CS ↑)) ≈ insʷ 3 ((CS ↑) • CS)
wn00103 = win 3 0 complete₃ (CS • (CS ↑)) ((CS ↑) • CS) _ _ Eq.refl
wn00104 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) ≈ insʷ 3 (CCZ)
wn00104 = win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) _ _ Eq.refl
wn00105 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((CX₁₀ ↑) • (CX₁₀ ↑))
wn00105 = win 0 3 complete₃ (ε) ((CX₁₀ ↑) • (CX₁₀ ↑)) _ _ Eq.refl
wn00106 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CZ • Swap ↑) • CS)
wn00106 = win 0 3 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) _ _ Eq.refl
wn00107 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 0 ((CZ ↑) • Swap)
wn00107 = win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) _ _ Eq.refl
wn00108 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (CZ ↑)) ≈ insʷ 0 ((Swap ↑ • CZ • Swap ↑) • Swap)
wn00108 = win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) _ _ Eq.refl
wn00109 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS • CS • CS) • (CZ ↑)) ≈ insʷ 3 ((CZ ↑) • (CS • CS • CS))
wn00109 = win 3 0 complete₃ ((CS • CS • CS) • (CZ ↑)) ((CZ ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00110 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • (CZ ↑)) ≈ insʷ 3 ((CZ ↑) • CS)
wn00110 = win 3 0 complete₃ (CS • (CZ ↑)) ((CZ ↑) • CS) _ _ Eq.refl
wn00111 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑))
wn00111 = win 0 3 complete₃ (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00112 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (CX₁₀ ↑)) ≈ insʷ 3 ((CX₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑))
wn00112 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CX₁₀ ↑)) ((CX₁₀ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00113 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 0 ((CX₁₀ ↑) • Swap)
wn00113 = win 0 3 complete₃ (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) _ _ Eq.refl
wn00114 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (CX₁₀ ↑)) ≈ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • Swap)
wn00114 = win 0 3 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00115 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (ε) ≈ insʷ 0 ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑))
wn00115 = win 0 3 complete₃ (ε) ((Swap ↑ • CX₀₁ • Swap ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) _ _ Eq.refl
wn00116 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 (K • (K • iI))
wn00116 = win 3 0 complete₃ (ε) (K • (K • iI)) _ _ Eq.refl
wn00117 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • CK₁₀ • K) ≈ insʷ 3 (CK₁₀)
wn00117 = win 3 0 complete₃ ((K • iI) • CK₁₀ • K) (CK₁₀) _ _ Eq.refl
wn00118 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (K • Swap) ≈ insʷ 3 (Swap • (K ↑))
wn00118 = win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) _ _ Eq.refl
wn00119 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • Swap) ≈ insʷ 3 (Swap • ((K • iI) ↑))
wn00119 = win 3 0 complete₃ ((K • iI) • Swap) (Swap • ((K • iI) ↑)) _ _ Eq.refl
wn00120 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((K • iI) • CCZ • K) ≈ insʷ 0 (Toff)
wn00120 = win 0 3 complete₃ ((K • iI) • CCZ • K) (Toff) _ _ Eq.refl
wn00121 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (K ↑)) ≈ insʷ 3 (K • Swap)
wn00121 = win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) _ _ Eq.refl
wn00122 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (iI ↑)) ≈ insʷ 3 (iI • Swap)
wn00122 = win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) _ _ Eq.refl
wn00123 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • K) ≈ insʷ 3 ((K ↑) • Swap)
wn00123 = win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) _ _ Eq.refl
wn00124 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • iI) ≈ insʷ 3 ((iI ↑) • Swap)
wn00124 = win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) _ _ Eq.refl
wn00125 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) ≈ insʷ 0 (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI)
wn00125 = win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) _ _ Eq.refl
wn00126 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • (S ↑ • CK₁₀) • K) ≈ insʷ 3 ((S ↑ • CK₁₀))
wn00126 = win 3 0 complete₃ ((K • iI) • (S ↑ • CK₁₀) • K) ((S ↑ • CK₁₀)) _ _ Eq.refl
wn00127 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (iI • Swap) ≈ insʷ 3 (Swap • (iI ↑))
wn00127 = win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) _ _ Eq.refl
wn00128 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Toff) ≈ insʷ 0 (K • CCZ • (K • iI))
wn00128 = win 0 3 complete₃ (Toff) (K • CCZ • (K • iI)) _ _ Eq.refl
wn00129 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • ((K • iI) ↑)) ≈ insʷ 3 ((K • iI) • Swap)
wn00129 = win 3 0 complete₃ (Swap • ((K • iI) ↑)) ((K • iI) • Swap) _ _ Eq.refl
wn00130 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (CS ↑) • Swap) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑))
wn00130 = win 0 3 complete₃ (Swap • (CS ↑) • Swap) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00131 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑)) ≈ insʷ 3 ((CS • CS • CS))
wn00131 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑)) ((CS • CS • CS)) _ _ Eq.refl
wn00132 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) ≈ insʷ 3 (CS)
wn00132 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) _ _ Eq.refl
wn00133 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn00133 = win 3 0 complete₃ ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00134 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • CK₁₀ • (Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑))
wn00134 = win 3 0 complete₃ ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00135 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) ≈ insʷ 0 (CS)
wn00135 = win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) _ _ Eq.refl
wn00136 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) ≈ insʷ 0 (CX₁₀)
wn00136 = win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) _ _ Eq.refl
wn00137 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) ≈ insʷ 3 (Swap • ((S ↑ • CK₁₀) ↑))
wn00137 = win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) _ _ Eq.refl
wn00138 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn00138 = win 0 3 complete₃ ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00139 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • ((S ↑ • CK₁₀) ↑)) ≈ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap)
wn00139 = win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) _ _ Eq.refl
wn00140 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) ≈ insʷ 3 (Swap • (CK₁₀ ↑))
wn00140 = win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) _ _ Eq.refl
wn00141 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • CK₁₀ • (Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CK₁₀ • Swap ↑))
wn00141 = win 0 3 complete₃ ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) _ _ Eq.refl
wn00142 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (CK₁₀ ↑)) ≈ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • Swap)
wn00142 = win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) _ _ Eq.refl
wn00143 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CS ↑) • (Swap ↑)) ≈ insʷ 3 ((CS ↑))
wn00143 = win 3 0 complete₃ ((Swap ↑) • (CS ↑) • (Swap ↑)) ((CS ↑)) _ _ Eq.refl
wn00144 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) ≈ insʷ 3 (CX₁₀)
wn00144 = win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) _ _ Eq.refl
wn00145 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • (CS • CS • CS) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00145 = win 3 0 complete₃ ((Swap ↑) • (CS • CS • CS) • (Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00146 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • CS • (Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑))
wn00146 = win 3 0 complete₃ ((Swap ↑) • CS • (Swap ↑)) ((Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00147 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ≈ insʷ 3 (CCZ)
wn00147 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) (CCZ) _ _ Eq.refl
wn00148 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (ε) ≈ insʷ 3 ((K • iI) • (S • S • S) • K • (K • iI) • S • K)
wn00148 = win 3 0 complete₃ (ε) ((K • iI) • (S • S • S) • K • (K • iI) • S • K) _ _ Eq.refl
wn00149 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • K • Toff • (K • iI) • (S • S • S) • K) ≈ insʷ 3 (Toff)
wn00149 = win 3 0 complete₃ ((K • iI) • S • K • Toff • (K • iI) • (S • S • S) • K) (Toff) _ _ Eq.refl
wn00150 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • K • (Swap ↑ • CS • Swap ↑) • (K • iI) • (S • S • S) • K) ≈ insʷ 3 ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑))
wn00150 = win 3 0 complete₃ ((K • iI) • S • K • (Swap ↑ • CS • Swap ↑) • (K • iI) • (S • S • S) • K) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) _ _ Eq.refl
wn00151 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (S ↑)) ≈ insʷ 0 ((S ↑ ↑) • (Swap ↑))
wn00151 = win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00152 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K • iI) • S • K • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (K • iI) • (S • S • S) • K) ≈ insʷ 3 (((S • S • S) ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑))
wn00152 = win 3 0 complete₃ ((K • iI) • S • K • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (K • iI) • (S • S • S) • K) (((S • S • S) ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) _ _ Eq.refl
wn00153 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • ((S • S • S) ↑)) ≈ insʷ 0 (((S • S • S) ↑ ↑) • (Swap ↑))
wn00153 = win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00154 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑ ↑) • ((S • S • S) ↑ ↑)) ≈ insʷ 0 (ε)
wn00154 = win 0 3 complete₃ ((S ↑ ↑) • ((S • S • S) ↑ ↑)) (ε) _ _ Eq.refl
wn00155 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff) ≈ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀)
wn00155 = win 3 0 complete₃ (Toff) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) _ _ Eq.refl
wn00156 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ≈ insʷ 0 ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑))
wn00156 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00157 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ≈ insʷ 0 ((CX₀₁ ↑) • Swap)
wn00157 = win 0 3 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) _ _ Eq.refl
wn00158 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (Swap • (CX₀₁ ↑)) ≈ insʷ 0 ((Swap ↑ • CX₀₁ • Swap ↑) • Swap)
wn00158 = win 0 3 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) _ _ Eq.refl
wn00159 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀) ≈ insʷ 0 ((S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑))
wn00159 = win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀) ((S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00160 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ≈ insʷ 3 ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑))
wn00160 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) _ _ Eq.refl
wn00161 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ≈ insʷ 3 (ε)
wn00161 = win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) (ε) _ _ Eq.refl
wn00162 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ≈ insʷ 3 (Toff)
wn00162 = win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) (Toff) _ _ Eq.refl
wn00163 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CCZ) ≈ insʷ 0 (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑))
wn00163 = win 0 3 complete₃ (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00164 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CZ • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • CZ)
wn00164 = win 3 0 complete₃ (CZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CZ) _ _ Eq.refl
wn00165 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ)
wn00165 = win 3 0 complete₃ (CZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CZ) _ _ Eq.refl
wn00166 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 (CCZ)
wn00166 = win 0 3 complete₃ (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) _ _ Eq.refl
wn00167 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CZ • (CS ↑)) ≈ insʷ 3 ((CS ↑) • CZ)
wn00167 = win 3 0 complete₃ (CZ • (CS ↑)) ((CS ↑) • CZ) _ _ Eq.refl
wn00168 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CZ • ((CS • CS • CS) ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • CZ)
wn00168 = win 3 0 complete₃ (CZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CZ) _ _ Eq.refl
wn00169 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (S ↑ • CK₁₀)) ≈ insʷ 3 ((S ↑ • CK₁₀) • (CS ↑))
wn00169 = win 3 0 complete₃ ((CS ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • (CS ↑)) _ _ Eq.refl
wn00170 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (S ↑ • CK₁₀)) ≈ insʷ 3 ((S ↑ • CK₁₀) • ((CS • CS • CS) ↑))
wn00170 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00171 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑) • Toff • (Swap ↑)) ≈ insʷ 3 (Toff)
wn00171 = win 3 0 complete₃ ((Swap ↑) • Toff • (Swap ↑)) (Toff) _ _ Eq.refl
wn00172 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • CZ) ≈ insʷ 3 (CZ • CCZ)
wn00172 = win 3 0 complete₃ (CCZ • CZ) (CZ • CCZ) _ _ Eq.refl
wn00173 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((X ↑ ↑) • (Swap ↑)) ≈ insʷ 0 ((Swap ↑) • (X ↑))
wn00173 = win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) _ _ Eq.refl
wn00174 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00174 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00175 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑) • (X ↑)) ≈ insʷ 0 ((X ↑ ↑) • (Swap ↑))
wn00175 = win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) _ _ Eq.refl
wn00176 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00176 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00177 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (CS ↑)) ≈ insʷ 3 ((CS ↑) • CCZ)
wn00177 = win 3 0 complete₃ (CCZ • (CS ↑)) ((CS ↑) • CCZ) _ _ Eq.refl
wn00178 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (CZ ↑)) ≈ insʷ 3 ((CZ ↑) • CCZ)
wn00178 = win 3 0 complete₃ (CCZ • (CZ ↑)) ((CZ ↑) • CCZ) _ _ Eq.refl
wn00179 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS))
wn00179 = win 0 3 complete₃ ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00180 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • ((CS • CS • CS) ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • CCZ)
wn00180 = win 3 0 complete₃ (CCZ • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CCZ) _ _ Eq.refl
wn00181 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS))
wn00181 = win 0 3 complete₃ ((CS • CS • CS) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00182 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff • (X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • Toff • (X ↑ ↑) • Toff)
wn00182 = win 3 0 complete₃ (Toff • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00183 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • S)
wn00183 = win 3 0 complete₃ (S • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • S) _ _ Eq.refl
wn00184 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S)
wn00184 = win 3 0 complete₃ (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S) _ _ Eq.refl
wn00185 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (S • S • S))
wn00185 = win 3 0 complete₃ ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00186 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S))
wn00186 = win 3 0 complete₃ ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S)) _ _ Eq.refl
wn00187 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Toff • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • Toff)
wn00187 = win 3 0 complete₃ (Toff • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • Toff) _ _ Eq.refl
wn00188 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • Z) ≈ insʷ 3 (Z • CCZ)
wn00188 = win 3 0 complete₃ (CCZ • Z) (Z • CCZ) _ _ Eq.refl
wn00189 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CZ • Swap ↑) • Swap) ≈ insʷ 3 (Swap • (CZ ↑))
wn00189 = win 3 0 complete₃ ((Swap ↑ • CZ • Swap ↑) • Swap) (Swap • (CZ ↑)) _ _ Eq.refl
wn00190 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • CZ) ≈ insʷ 0 (CZ • (Swap ↑ • CS • Swap ↑))
wn00190 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CZ) (CZ • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00191 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (Swap • (CZ ↑)) ≈ insʷ 3 ((Swap ↑ • CZ • Swap ↑) • Swap)
wn00191 = win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) _ _ Eq.refl
wn00192 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS • CS • CS) • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CZ • Swap ↑) • (CS • CS • CS))
wn00192 = win 3 0 complete₃ ((CS • CS • CS) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00193 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • (Swap ↑ • CZ • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CZ • Swap ↑) • CS)
wn00193 = win 3 0 complete₃ (CS • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • CS) _ _ Eq.refl
wn00194 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑))
wn00194 = win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00195 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑))
wn00195 = win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) _ _ Eq.refl
wn00196 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ≈ insʷ 3 ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI)
wn00196 = win 3 0 complete₃ ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) _ _ Eq.refl
wn00197 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff • (X ↑ ↑)) ≈ insʷ 3 ((X ↑ ↑) • Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI))
wn00197 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00198 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ≈ insʷ 0 ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑))
wn00198 = win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (CS • CS • CS)) ((CS • CS • CS) • (Swap ↑ • CS • Swap ↑)) _ _ Eq.refl
wn00199 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS • CS • CS) • ((CS • CS • CS) ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • (CS • CS • CS))
wn00199 = win 3 0 complete₃ ((CS • CS • CS) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (CS • CS • CS)) _ _ Eq.refl
wn00200 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CS • ((CS • CS • CS) ↑)) ≈ insʷ 3 (((CS • CS • CS) ↑) • CS)
wn00200 = win 3 0 complete₃ (CS • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • CS) _ _ Eq.refl
wn00201 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • S) ≈ insʷ 3 (S • (K ↑ • CCZ • K ↑ • iI))
wn00201 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • S) (S • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00202 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (S • S • S)) ≈ insʷ 3 ((S • S • S) • (K ↑ • CCZ • K ↑ • iI))
wn00202 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (S • S • S)) ((S • S • S) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00203 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • S) ≈ insʷ 3 (S • (CS ↑))
wn00203 = win 3 0 complete₃ ((CS ↑) • S) (S • (CS ↑)) _ _ Eq.refl
wn00204 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (S • S • S)) ≈ insʷ 3 ((S • S • S) • (CS ↑))
wn00204 = win 3 0 complete₃ ((CS ↑) • (S • S • S)) ((S • S • S) • (CS ↑)) _ _ Eq.refl
wn00205 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • (CS ↑))
wn00205 = win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (CS ↑)) _ _ Eq.refl
wn00206 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • S) ≈ insʷ 3 (S • ((CS • CS • CS) ↑))
wn00206 = win 3 0 complete₃ (((CS • CS • CS) ↑) • S) (S • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00207 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (S • S • S)) ≈ insʷ 3 ((S • S • S) • ((CS • CS • CS) ↑))
wn00207 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (S • S • S)) ((S • S • S) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00208 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 3 ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑))
wn00208 = win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((CS • CS • CS) ↑)) _ _ Eq.refl
wn00209 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((K ↑ • CCZ • K ↑ • iI) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ≈ insʷ 3 ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI))
wn00209 = win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑) • (K ↑ • CCZ • K ↑ • iI)) _ _ Eq.refl
wn00210 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • (S ↑))
wn00210 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00211 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑))
wn00211 = win 0 3 complete₃ ((S ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑)) _ _ Eq.refl
wn00212 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑))
wn00212 = win 0 3 complete₃ (((S • S • S) ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00213 : (₁₊ (0 +ℕ 3)) ⊢ insʷ 0 (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ≈ insʷ 0 ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑))
wn00213 = win 0 3 complete₃ (((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑)) _ _ Eq.refl
wn00214 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 (CCZ • (S • S • S)) ≈ insʷ 3 ((S • S • S) • CCZ)
wn00214 = win 3 0 complete₃ (CCZ • (S • S • S)) ((S • S • S) • CCZ) _ _ Eq.refl
wn00215 : (₁₊ (3 +ℕ 0)) ⊢ insʷ 3 ((X ↑ ↑) • (Swap ↑)) ≈ insʷ 3 ((Swap ↑) • (X ↑))
wn00215 = win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) _ _ Eq.refl
