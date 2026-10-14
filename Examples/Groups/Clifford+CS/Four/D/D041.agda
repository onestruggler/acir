{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D041 where

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


-- comm CCZ023 CCZ012: 177 steps (scratchpad/four/lower.py)
lem-comm-CCZ023-CCZ012 : ⟪ (CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CCZ012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (run b22))))))))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ CCZ012 ∷ []) (CCZ023 ∷ CCZ012 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b0 = at 2 0 (CX31 ∷ CX31 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (CCZ012 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (ε) (CCZ • CCZ) tt tt Eq.refl) ▸
       at 4 0 (CX31 ∷ CX31 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ023 ∷ CCZ012 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CCZ012 ∷ CX31 ∷ Sw12 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b1 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CCZ023 ∷ CCZ012 ∷ CX31 ∷ Sw12 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CCZ012 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b2 = at 2 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 3 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ023 ∷ CCZ012 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b3 = at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b4 = at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b5 : Chain (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b5 = at 3 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸ done

  b6 : Chain (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b6 = at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 10 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b7 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CCZ023 ∷ CCZ012 ∷ CCZ012 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b8 = at 4 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b9 : Chain (CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b9 = at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b10 = at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b11 : Chain (CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b11 = at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b12 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b12 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b13 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ [])
  b13 = at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b14 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CX31 ∷ CCZ012 ∷ CX31 ∷ []) (CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ [])
  b14 = at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b15 : Chain (CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ []) (CX31 ∷ Sw12 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ [])
  b15 = at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 2 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (CX31 ∷ Sw12 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ [])
  b16 = at 0 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 1 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b17 : Chain (CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ []) (CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ [])
  b17 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b18 : Chain (CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ []) (CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ [])
  b18 = at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b19 : Chain (CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ []) (CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b19 = at 1 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸ done

  b20 : Chain (CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ [])
  b20 = at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b21 : Chain (CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ []) (CCZ012 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ [])
  b21 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (CCZ012 ∷ CCZ023 ∷ Sw12 ∷ Sw12 ∷ []) (CCZ012 ∷ CCZ023 ∷ [])
  b22 = at 2 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

