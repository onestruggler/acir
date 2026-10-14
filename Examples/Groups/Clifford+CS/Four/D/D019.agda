{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D019 where

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


-- N23-D: 14 steps (scratchpad/four/lower.py)
lem-N23-D : ⟪ (CX23 ∷ CCZ012 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-N23-D = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ CCZ012 ∷ CX23 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ Sw01 ∷ CX23 ∷ CS12 ∷ Sw01 ∷ CX23 ∷ [])
  b0 = at 1 1 (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (CS01 ∷ CX23 ∷ []) (sym (low-comm (CS) (CX₀₁))) ▸
       at 1 2 (CX21 ∷ CX23 ∷ []) (win 0 3 complete₃ ((CX₀₁ ↑) • CX₁₀) (CX₁₀ • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01⁻ ∷ CX23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CX₀₁))) ▸
       at 3 2 (CX21 ∷ CX23 ∷ []) (win 0 3 complete₃ ((CX₀₁ ↑) • CX₁₀) (CX₁₀ • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX23 ∷ []) (sym (low-comm (Swap) (CX₀₁))) ▸ done

  b1 : Chain (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ Sw01 ∷ CX23 ∷ CS12 ∷ Sw01 ∷ CX23 ∷ []) (CCZ012 ∷ [])
  b1 = at 5 2 (CS12 ∷ CX23 ∷ []) (win 0 3 complete₃ ((CX₀₁ ↑) • CS) (CS • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁)) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((CX₀₁ ↑) • (CX₀₁ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (CX₁₀ ↑) • (CS • CS • CS) • (CX₁₀ ↑) • (Swap ↑ • CS • Swap ↑)) (CCZ) tt tt Eq.refl) ▸ done

