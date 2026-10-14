{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D061 where

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
open import Examples.Groups.Clifford+CS.Four.D.D060 using (lem-CCZ123-passes-CKd10)
open import Examples.Groups.Clifford+CS.Four.D.D046 using (lem-ROT≡cF)
open import Examples.Groups.Clifford+CS.Four.D.D014 using (lem-comm-CCZ123-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D058 using (lem-comm-CZ01-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D059 using (lem-comm-CZ01-CCZ123)

-- X0-ROT: 427 steps (scratchpad/four/lower.py)
lem-X0-ROT : ⟪ (X0 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-X0-ROT = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (run b53)))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ X0 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ [])
  b0 = at 1 15 (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF) ▸
       at 4 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 3 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 2 0 (X0 ∷ X0 ∷ []) (win 3 0 complete₃ (ε) (X • X) tt tt Eq.refl) ▸
       at 0 3 (CK10 ∷ CZ01 ∷ CX10 ∷ []) (win 3 0 complete₃ (X • CK₁₀ • X) (CK₁₀ • CZ • CX₁₀) tt tt Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ X0 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ X0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ [])
  b1 = at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b2 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ X0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ X0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ X1 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ [])
  b2 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ X0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ X1 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ CCZ123 ∷ CZ23 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ [])
  b3 = at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 4 3 (CCZ123 ∷ CZ23 ∷ []) (win 0 3 complete₃ (X • CCZ • X) (CCZ • (CZ ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ CCZ123 ∷ CZ23 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CZ23 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ [])
  b4 = at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CZ23 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ [])
  b5 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ Sw01 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ [])
  b6 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸ done

  b7 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ Sw01 ∷ Sw01 ∷ X0 ∷ CK10⁻ ∷ X0 ∷ X0 ∷ CCZ023 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ X0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ [])
  b7 = at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 3 (CX10 ∷ CZ01 ∷ CK10⁻ ∷ []) (win 3 0 complete₃ (X • (S ↑ • CK₁₀) • X) (CX₁₀ • CZ • (S ↑ • CK₁₀)) tt tt Eq.refl) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b8 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ X0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ X0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ [])
  b8 = at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b9 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ X0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ X0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X1 ∷ Sw01 ∷ [])
  b9 = at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ X0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ X1 ∷ Sw01 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ23 ∷ Sw01 ∷ [])
  b10 = at 9 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 10 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 10 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 9 3 (CCZ123 ∷ CZ23 ∷ []) (win 0 3 complete₃ (X • CCZ • X) (CCZ • (CZ ↑)) tt tt Eq.refl) ▸
       at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b11 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ23 ∷ Sw01 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ [])
  b11 = at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b12 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ [])
  b12 = at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b13 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CZ23 ∷ CX10 ∷ CZ01 ∷ CK10⁻ ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CX10 ∷ Sw12 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b13 = at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX10 ∷ CZ23 ∷ []) (sym (low-comm (CX₁₀) (CZ))) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b14 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CCZ023 ∷ CX10 ∷ Sw12 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b14 = at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b15 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b15 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸ done

  b16 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b16 = at 9 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 7 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b17 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b17 = at 3 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b18 : Chain (CK10 ∷ CZ01 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ CX20 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ CX20 ∷ CCZ013 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b18 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b19 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ CX20 ∷ CCZ013 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b19 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b20 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b20 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b21 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CCZ012 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b21 = at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b22 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CCZ012 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CX30 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b22 = at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CX30 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b23 = at 9 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b24 = at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b25 = at 12 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b26 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ Sw12 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b26 = at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 6 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b27 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b27 = at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b28 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b29 = at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b30 = at 10 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 13 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b31 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b31 = at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b32 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ CCZ023 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b32 = at 6 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b33 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Sw01 ∷ CCZ023 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b33 = at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b34 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b34 = at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b35 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b35 = at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b36 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b36 = at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b37 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b37 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b38 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b39 = at 4 2 (CS23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b40 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b40 = at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b41 : Chain (CK10 ∷ CZ01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b41 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b42 : Chain (CK10 ∷ CZ01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b42 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b43 : Chain (CK10 ∷ CZ01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b43 = at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b44 : Chain (CK10 ∷ CZ01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CZ01 ∷ CCZ023 ∷ CS13 ∷ Sw12 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b44 = at 8 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b45 : Chain (CK10 ∷ CZ01 ∷ CCZ023 ∷ CS13 ∷ Sw12 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CZ01 ∷ CCZ123 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ [])
  b45 = at 4 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CZ01 ∷ []) (lem-comm-CZ01-CCZ023) ▸ done

  b46 : Chain (CK10 ∷ CCZ023 ∷ CZ01 ∷ CCZ123 ∷ CZ23 ∷ CZ01 ∷ CK10⁻ ∷ CCZ023 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ [])
  b46 = at 2 2 (CCZ123 ∷ CZ01 ∷ []) (lem-comm-CZ01-CCZ123) ▸
       at 3 2 (CZ23 ∷ CZ01 ∷ []) (low-comm (CZ) (CZ)) ▸
       at 4 2 [] (win 3 0 complete₃ (CZ • CZ) (ε) tt tt Eq.refl) ▸
       at 3 2 (CK10⁻ ∷ CZ23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CZ))) ▸
       at 2 2 (CK10⁻ ∷ CCZ123 ∷ []) (lem-CCZ123-passes-CKd10) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b47 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CZ23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ [])
  b47 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b48 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CZ23 ∷ [])
  b48 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b49 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CZ23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ23 ∷ Sw01 ∷ CZ23 ∷ [])
  b49 = at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 5 2 (CCZ123 ∷ CZ23 ∷ []) (win 0 3 complete₃ ((CZ ↑) • CCZ) (CCZ • (CZ ↑)) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b50 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ23 ∷ Sw01 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ CZ23 ∷ [])
  b50 = at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b51 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ CZ23 ∷ [])
  b51 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b52 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ CZ23 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CCZ023 ∷ CZ23 ∷ CZ23 ∷ [])
  b52 = at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b53 : Chain (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ123 ∷ CCZ023 ∷ CZ23 ∷ CZ23 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CCZ123 ∷ [])
  b53 = at 3 2 (CCZ023 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ023) ▸
       at 5 2 [] (win 0 3 complete₃ ((CZ ↑) • (CZ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 4 (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (sym lem-ROT≡cF) ▸ done

