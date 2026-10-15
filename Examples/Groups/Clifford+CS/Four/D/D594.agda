{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D594 where

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
open import Examples.Groups.Clifford+CS.Four.D.D593 using (lem-pass-X0-X3-TOFF302-X0-X3-vs-X2-TOFF312-X2)
-- pass [TOFF312] [X0 X2 X3 TOFF302 X0 X2 X3]: 149 steps
lem-pass-TOFF312-vs-X0-X2-X3-TOFF302-X0-X2-X3 : ⟪ (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ Toff302 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff302 ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X0-X2-X3-TOFF302-X0-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (run b18))))))))))))))))))
  where
  b0 : Chain (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ Toff302 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ [])
  b0 = at 0 1 (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (win 0 3 complete₃ (Toffᵗ) ((X ↑) • (X ↑) • Toffᵗ • (X ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 12 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 10 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸ done

  b1 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ [])
  b1 = at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b2 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι1 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ [])
  b2 = at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 15 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 16 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 15 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b3 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι1 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ [])
  b3 = at 14 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 8 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸ done

  b4 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ Sw01 ∷ X3 ∷ Toff312 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b4 = at 9 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 9 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 6 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 5 8 (X1 ∷ X3 ∷ Toff312 ∷ X1 ∷ X3 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • X • (X ↑) • (X ↑ ↑) • Toffᵗ • X • (X ↑) • (X ↑ ↑)) (X • (X ↑ ↑) • Toffᵗ • X • (X ↑ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ Sw01 ∷ X3 ∷ Toff312 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b5 = at 5 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 7 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Sw01 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b6 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 13 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸ done

  b7 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Sw01 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b7 = at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b8 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Toff302 ∷ X0 ∷ X3 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ [])
  b8 = at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 14 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 7 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 8 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b9 : Chain (X2 ∷ X2 ∷ Toff312 ∷ X2 ∷ X0 ∷ X3 ∷ Toff302 ∷ X0 ∷ X3 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ X0 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b9 = at 9 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 1 8 (X0 ∷ X3 ∷ Toff302 ∷ X0 ∷ X3 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) (sym lem-pass-X0-X3-TOFF302-X0-X3-vs-X2-TOFF312-X2) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 4 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (X2 ∷ X0 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X2 ∷ X0 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b10 = at 3 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b11 : Chain (X2 ∷ X0 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X2 ∷ X0 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι1 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b11 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (X2 ∷ X0 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι1 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X2 ∷ X0 ∷ X3 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b12 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b13 : Chain (X2 ∷ X0 ∷ X3 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X0 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b13 = at 3 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 4 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 6 (X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • X • (X ↑ ↑) • Toffᵗ • X • (X ↑ ↑)) (X • (X ↑) • (X ↑ ↑) • Toffᵗ • X • (X ↑) • (X ↑ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸ done

  b14 : Chain (X0 ∷ Sw01 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b14 = at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 2 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b15 : Chain (X0 ∷ X2 ∷ X3 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b15 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b16 : Chain (X0 ∷ X2 ∷ X3 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b16 = at 4 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b17 : Chain (X0 ∷ X2 ∷ X3 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw01 ∷ X1 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff302 ∷ X0 ∷ Sw01 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ [])
  b17 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 4 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸ done

  b18 : Chain (X0 ∷ X2 ∷ X3 ∷ Toff302 ∷ X0 ∷ Sw01 ∷ X2 ∷ X3 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff312 ∷ X2 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff302 ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ [])
  b18 = at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 6 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 5 (Toff312 ∷ []) (win 0 3 complete₃ ((X ↑) • (X ↑) • Toffᵗ • (X ↑) • (X ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done

