{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D060 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain


-- CCZ123 passes CKd10: 15 steps (scratchpad/four/lower.py)
lem-CCZ123-passes-CKd10 : ⟪ (CCZ123 ∷ CK10⁻ ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ123-passes-CKd10 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ CK10⁻ ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CK10⁻ ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CK10⁻ ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (CK10⁻ ∷ CCZ123 ∷ [])
  b1 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CK10⁻ ∷ CX32 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₁₀))) ▸
       at 2 2 (CK10⁻ ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 1 2 (CK10⁻ ∷ CX32 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₁₀))) ▸
       at 0 2 (CK10⁻ ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (S ↑ • CK₁₀)) ((S ↑ • CK₁₀) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) tt tt Eq.refl) ▸ done

