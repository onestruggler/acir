{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D002 where

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


-- CCZ123-CX30: 61 steps (scratchpad/four/lower.py)
lem-CCZ123-CX30 : ⟪ (CCZ123 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ123-CX30 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CCZ123 ∷ CX30 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ (CCZ) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS13 ∷ [])
  b1 = at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CS13 ∷ [])
  b2 = at 5 2 (CX10 ∷ CX23 ∷ []) (sym (low-comm (CX₁₀) (CX₀₁))) ▸
       at 6 2 (Sw12 ∷ CX13 ∷ []) (win 0 3 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b3 : Chain (CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ [])
  b3 = at 4 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 3 2 (CX31 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (CS23 ∷ CX12 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ [])
  b4 = at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CX23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (CS23 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ [])
  b5 = at 3 2 (CX10 ∷ CX23 ∷ []) (sym (low-comm (CX₁₀) (CX₀₁))) ▸
       at 4 2 (Sw12 ∷ CX13 ∷ []) (win 0 3 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b6 : Chain (CS23 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ [])
  b6 = at 2 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 2 (CX31 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CX30 ∷ CCZ123 ∷ [])
  b7 = at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) (CCZ) tt tt Eq.refl) ▸ done

