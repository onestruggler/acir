{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D131 where

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
open import Examples.Groups.Clifford+CS.Four.D.D130 using (lem-pass-CCZ123-vs-TOFF013)
-- pass [CCZ023] [X3 TOFF013 X3]: 686 steps
lem-pass-CCZ023-vs-X3-TOFF013-X3 : ⟪ (CCZ023 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-X3-TOFF013-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (run b85)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CCZ023 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (CCZ023 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CCZ023 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CCZ023 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ023 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (CCZ023 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b3 : Chain (CCZ023 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ []) (CCZ023 ∷ CX10 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ [])
  b3 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX10 ∷ Toff012 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) tt tt Eq.refl) ▸
       at 1 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b4 : Chain (CCZ023 ∷ CX10 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (CCZ023 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b5 : Chain (CCZ023 ∷ CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (CCZ023 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ [])
  b5 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (CCZ023 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ []) (CCZ023 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b7 : Chain (CCZ023 ∷ CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (CX10 ∷ CX10 ∷ CCZ023 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ [])
  b7 = at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 0 (CX10 ∷ CX10 ∷ []) (win 3 0 complete₃ (ε) (CX₁₀ • CX₁₀) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CX10 ∷ CX10 ∷ CCZ023 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ [])
  b8 = at 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (CX10 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ [])
  b9 = at 7 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 6 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b10 : Chain (CX10 ∷ CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ [])
  b10 = at 7 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b11 : Chain (CX10 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ [])
  b11 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b12 : Chain (CX10 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX20 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ CX20 ∷ CCZ013 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b12 = at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CX10 ∷ Sw12 ∷ CX20 ∷ CCZ013 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b13 = at 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b14 : Chain (CX10 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b14 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b15 : Chain (CX10 ∷ Sw12 ∷ CX20 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX30 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b15 = at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b16 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ CX30 ∷ CCZ012 ∷ CX30 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ CX30 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b16 = at 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸ done

  b17 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ CX30 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CX21 ∷ Sw23 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b17 = at 6 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸ done

  b18 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CX21 ∷ Sw23 ∷ CCZ012 ∷ CX31 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b18 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b19 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b19 = at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CX32 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸ done

  b20 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CX32 ∷ CCZ012 ∷ CX32 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b20 = at 5 3 (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ CCZ013 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b21 = at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b22 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b23 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b23 = at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b24 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b24 = at 12 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CCZ023 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b25 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b26 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ CCZ012 ∷ CCZ023 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ CCZ023 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b26 = at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ CCZ023 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b27 = at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b28 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b28 = at 10 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b29 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b29 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b30 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b30 = at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b31 : Chain (CX10 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b31 = at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b32 : Chain (CX10 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b32 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b33 : Chain (CX10 ∷ Sw12 ∷ CCZ013 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ CCZ013 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ [])
  b33 = at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b34 : Chain (CX10 ∷ Sw12 ∷ CCZ013 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ [])
  b34 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b35 : Chain (CX10 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ [])
  b35 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸ done

  b36 : Chain (CX10 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ [])
  b36 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b37 : Chain (CX10 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ [])
  b37 = at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b38 : Chain (CX10 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ CCZ023 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Sw12 ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Toff013 ∷ [])
  b38 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b39 : Chain (CX10 ∷ CCZ023 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Sw12 ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Toff013 ∷ []) (CX10 ∷ Sw23 ∷ Toff012 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ [])
  b39 = at 5 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 2 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-TOFF013) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Toff012 ∷ Toff012 ∷ []) (win 3 0 complete₃ (ε) (Toff • Toff) tt tt Eq.refl) ▸ done

  b40 : Chain (CX10 ∷ Sw23 ∷ Toff012 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ [])
  b40 = at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b41 : Chain (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ [])
  b41 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b42 : Chain (CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ [])
  b42 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b43 : Chain (CX10 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ [])
  b43 = at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b44 : Chain (CX10 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ [])
  b44 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b45 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ [])
  b45 = at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b46 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ [])
  b46 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b47 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ [])
  b47 = at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b48 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ [])
  b48 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 10 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b49 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ [])
  b49 = at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b50 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ CCZ023 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b50 = at 4 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b51 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b51 = at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b52 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b52 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b53 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b53 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b54 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw01 ∷ Sw23 ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b54 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (CX10 ∷ Toff013 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b55 = at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b56 : Chain (CX10 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b56 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b57 : Chain (CX10 ∷ Toff013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ [])
  b57 = at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b58 : Chain (CX10 ∷ Toff013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CCZ023 ∷ Toff012 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b58 = at 2 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 11 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b59 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b59 = at 12 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b60 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b60 = at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b61 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b61 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸ done

  b62 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b62 = at 10 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 8 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b63 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b63 = at 4 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b64 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b64 = at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 9 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b65 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b65 = at 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸ done

  b66 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ K0 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b66 = at 3 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b67 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b67 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b68 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b68 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b69 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b69 = at 10 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b70 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ [])
  b70 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b71 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ [])
  b71 = at 4 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b72 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ [])
  b72 = at 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b73 : Chain (CX10 ∷ Toff013 ∷ Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ [])
  b73 = at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 2 (CS23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b74 : Chain (CX10 ∷ Toff013 ∷ CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ [])
  b74 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b75 : Chain (CX10 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ [])
  b75 = at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b76 : Chain (CX10 ∷ Toff013 ∷ Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ CCZ023 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CCZ123 ∷ [])
  b76 = at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b77 : Chain (CX10 ∷ Toff013 ∷ CCZ023 ∷ CS23 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ Toff013 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ [])
  b77 = at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b78 : Chain (CX10 ∷ Toff013 ∷ CCZ023 ∷ CCZ123 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b78 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b79 : Chain (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b79 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b80 : Chain (CX10 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b80 = at 8 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b81 : Chain (CX10 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ []) (X3 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b81 = at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 1 2 (X2 ∷ Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b82 : Chain (X3 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ []) (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b82 = at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b83 : Chain (X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b83 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b84 : Chain (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ []) (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ [])
  b84 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b85 : Chain (X3 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ CCZ023 ∷ CCZ123 ∷ CCZ123 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CCZ023 ∷ [])
  b85 = at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸ done

