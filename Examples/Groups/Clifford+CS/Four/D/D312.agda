{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D312 where

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
open import Examples.Groups.Clifford+CS.Four.D.D196 using (lem-pass-CCZ023-vs-CCZ123)
-- comm CCZ023 CZ13: 131 steps
lem-comm-CCZ023-CZ13 : ⟪ (CCZ023 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CZ13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ CZ13 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ13 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ13 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CZ13 ∷ [])
  b1 = at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CZ13 ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CZ13 ∷ [])
  b2 = at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 1 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ CCZ123 ∷ Sw01 ∷ CZ13 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ CZ13 ∷ [])
  b3 = at 1 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ CZ13 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CZ13 ∷ CS23 ∷ [])
  b4 = at 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 2 (CZ13 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CZ13 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CZ13 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CS23 ∷ [])
  b5 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CZ12 ∷ CX20 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS02 ∷ CX30 ∷ CS02⁻ ∷ CZ13 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ [])
  b6 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (CS02 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ []) (CS02 ∷ CX30 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ [])
  b7 = at 7 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CZ23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CZ23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CZ)) ▸
       at 4 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS02 ∷ CX30 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS23 ∷ []) (CS02 ∷ Sw23 ∷ CZ12 ∷ CX20 ∷ Sw23 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b8 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (CZ12 ∷ CX20 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (CS02 ∷ Sw23 ∷ CZ12 ∷ CX20 ∷ Sw23 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (Sw23 ∷ CS03 ∷ CZ12 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b9 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ CS03 ∷ CZ12 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ [])
  b10 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CZ23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 2 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (CZ13 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ [])
  b11 = at 2 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b12 : Chain (CZ13 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ []) (CZ13 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ [])
  b12 = at 5 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b13 : Chain (CZ13 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ []) (CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ [])
  b13 = at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b14 : Chain (CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b14 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b15 : Chain (CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b15 = at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b16 : Chain (CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (CZ13 ∷ CCZ023 ∷ [])
  b16 = at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CCZ023] [CZ13]: 1 steps
lem-pass-CCZ023-vs-CZ13 : ⟪ (CCZ023 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CZ13 = run b0
  where
  b0 : Chain (CCZ023 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ023 ∷ [])
  b0 = at 0 2 (CZ13 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CZ13) ▸ done


-- pass [TOFF302] [X2 TOFF312 X2]: 120 steps
lem-pass-TOFF302-vs-X2-TOFF312-X2 : ⟪ (Toff302 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff312 ∷ X2 ∷ Toff302 ∷ []) ⟫ʷ
lem-pass-TOFF302-vs-X2-TOFF312-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Toff302 ∷ X2 ∷ Toff312 ∷ X2 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ [])
  b0 = at 1 3 (K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (win 0 3 complete₃ ((X ↑) • Toffᵗ • (X ↑)) ((K ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • CCZ • ((K • iI) ↑ ↑)) tt tt Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 0 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b1 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ [])
  b1 = at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸ done

  b2 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ [])
  b2 = at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (Sw01 ∷ K3 ∷ CCZ123 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ [])
  b3 = at 4 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 0 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (win 0 3 complete₃ (Toffᵗ) ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ K3 ∷ CCZ123 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ [])
  b4 = at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b5 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ [])
  b5 = at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b6 : Chain (K3 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (K3 ∷ CCZ023 ∷ Sw01 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ [])
  b6 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (K3 ∷ CCZ023 ∷ Sw01 ∷ K3⁻ ∷ Sw01 ∷ K3 ∷ CZ13 ∷ CCZ123 ∷ K3⁻ ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CCZ023 ∷ K3⁻ ∷ Sw01 ∷ Sw01 ∷ [])
  b7 = at 2 2 (K3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((K • iI) ↑))) ▸
       at 3 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ (((K • iI) ↑ ↑) • (K ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CZ13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ13) ▸
       at 2 2 (CCZ123 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CCZ123) ▸
       at 3 0 (K3⁻ ∷ K3 ∷ []) (win 0 3 complete₃ (ε) (((K • iI) ↑ ↑) • (K ↑ ↑)) tt tt Eq.refl) ▸
       at 0 4 (X2 ∷ Toff312 ∷ X2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • CCZ • ((K • iI) ↑ ↑)) ((X ↑) • Toffᵗ • (X ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b8 : Chain (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CCZ023 ∷ K3⁻ ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ K3⁻ ∷ Sw01 ∷ [])
  b8 = at 5 2 (Sw01 ∷ K3⁻ ∷ []) (sym (low-comm (Swap) (((K • iI) ↑)))) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ K3⁻ ∷ Sw01 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3⁻ ∷ Sw01 ∷ [])
  b9 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3⁻ ∷ Sw01 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ Sw01 ∷ CCZ123 ∷ K3⁻ ∷ Sw01 ∷ [])
  b10 = at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ Sw01 ∷ CCZ123 ∷ K3⁻ ∷ Sw01 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b11 = at 3 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 4 3 (Toff312 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • CCZ • ((K • iI) ↑ ↑)) (Toffᵗ) tt tt Eq.refl) ▸
       at 4 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b12 : Chain (X2 ∷ Toff312 ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b12 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b13 : Chain (X2 ∷ Toff312 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b13 = at 4 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b14 : Chain (X2 ∷ Toff312 ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ Toff312 ∷ X2 ∷ Toff302 ∷ [])
  b14 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 4 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- groups [TOFF302] [X2 CKd23 X2]: 67 steps
lem-groups-TOFF302-vs-X2-CKd23-X2 : ⟪ (Toff302 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ Toff302 ∷ []) ⟫ʷ
lem-groups-TOFF302-vs-X2-CKd23-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Toff302 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (K3 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 2 (Sw01 ∷ CK23⁻ ∷ []) (sym (low-comm (Swap) ((S • CK₀₁)))) ▸
       at 1 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 0 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b1 : Chain (K3 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ [])
  b1 = at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ [])
  b2 = at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ [])
  b3 = at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 0 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ CK23⁻ ∷ X2 ∷ K3 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b4 = at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 4 (X2 ∷ CK23⁻ ∷ X2 ∷ Toff312 ∷ []) (win 0 3 complete₃ (Toffᵗ • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • Toffᵗ) tt tt Eq.refl) ▸
       at 0 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 1 2 (CK23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • CK₀₁))) ▸
       at 2 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b5 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ K3 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (X2 ∷ CK23⁻ ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b5 = at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b6 = at 9 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ [])
  b7 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 4 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸ done

  b8 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ CK23⁻ ∷ X2 ∷ Toff302 ∷ [])
  b8 = at 4 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [TOFF302] [X2 CKd23 X2]: 1 steps
lem-pass-TOFF302-vs-X2-CKd23-X2 : ⟪ (Toff302 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ Toff302 ∷ []) ⟫ʷ
lem-pass-TOFF302-vs-X2-CKd23-X2 = run b0
  where
  b0 : Chain (Toff302 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (X2 ∷ CK23⁻ ∷ X2 ∷ Toff302 ∷ [])
  b0 = at 0 4 (X2 ∷ CK23⁻ ∷ X2 ∷ Toff302 ∷ []) (lem-groups-TOFF302-vs-X2-CKd23-X2) ▸ done


-- groups [CK23 CS02 CS23 CX03 CSd23 CX03 CKd23] [X2 CKd21 X2]: 83 steps
lem-groups-CK23-CS02-CS23-CX03-CSd23-CX03-CKd23-vs-X2-CKd21-X2 : ⟪ (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) ⟫ʷ
lem-groups-CK23-CS02-CS23-CX03-CSd23-CX03-CKd23-vs-X2-CKd21-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ CK23⁻ ∷ [])
  b0 = at 6 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ (((S • CK₀₁) ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CX03 ∷ CK21⁻ ∷ X2 ∷ CK23⁻ ∷ [])
  b1 = at 6 2 (X2 ∷ CX13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (X ↑)) ((X ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CX03 ∷ CK21⁻ ∷ X2 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CK23⁻ ∷ [])
  b2 = at 6 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CK32⁻ ∷ CX01 ∷ []) (low-comm (CX₀₁) ((S ↑ • CK₁₀))) ▸
       at 7 2 (CK31⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CK21⁻ ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CK23⁻ ∷ [])
  b3 = at 7 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CK21⁻ ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CX03 ∷ CK23⁻ ∷ [])
  b4 = at 8 2 (X2 ∷ CX13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (X ↑)) ((X ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b5 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CX03 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ [])
  b5 = at 4 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CX03 ∷ CK21⁻ ∷ X2 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ [])
  b6 = at 4 2 (X2 ∷ CX13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (X ↑)) ((X ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CX03 ∷ CK21⁻ ∷ X2 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ [])
  b7 = at 4 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK32⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CK32⁻ ∷ CX01 ∷ []) (low-comm (CX₀₁) ((S ↑ • CK₁₀))) ▸
       at 5 2 (CK31⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b8 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CK21⁻ ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CK21⁻ ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ [])
  b8 = at 5 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CK21⁻ ∷ Sw01 ∷ CX13 ∷ X2 ∷ Sw01 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ [])
  b9 = at 6 2 (X2 ∷ CX13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • (X ↑)) ((X ↑) • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b10 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ [])
  b10 = at 2 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (CK₀₁ ↑)) tt tt Eq.refl) ▸ done


-- pass [TOFF302] [X2 CKd21 X2]: 95 steps
lem-pass-TOFF302-vs-X2-CKd21-X2 : ⟪ (Toff302 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff302 ∷ []) ⟫ʷ
lem-pass-TOFF302-vs-X2-CKd21-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Toff302 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 0 1 (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b1 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b2 = at 7 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (CK23 ∷ Sw01 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b3 = at 3 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 0 2 (Sw01 ∷ K3 ∷ []) (sym (low-comm (Swap) ((K ↑)))) ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ (Toffᵗ) ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 0 2 (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁)) ▸ done

  b4 : Chain (CK23 ∷ Sw01 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw01 ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b4 = at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b5 : Chain (CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw01 ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ [])
  b5 = at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CK23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • CK₀₁))) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 0 10 (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) (lem-groups-CK23-CS02-CS23-CX03-CSd23-CX03-CKd23-vs-X2-CKd21-X2) ▸ done

  b6 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CK23⁻ ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ [])
  b6 = at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CK23⁻ ∷ []) (sym (low-comm (Swap) ((S • CK₀₁)))) ▸
       at 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸ done

  b7 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ CK23 ∷ CS02 ∷ CS23 ∷ CX03 ∷ Sw01 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ [])
  b7 = at 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CK23 ∷ []) (sym (low-comm (Swap) (CK₀₁))) ▸ done

  b8 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ CK23 ∷ CS12 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CK23⁻ ∷ Sw01 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b8 = at 4 7 (Toff312 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • CS • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((S • CK₀₁) ↑)) (Toffᵗ) tt tt Eq.refl) ▸
       at 4 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b9 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 10 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸ done

  b10 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b10 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b11 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ Toff302 ∷ [])
  b11 = at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 11 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 4 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

