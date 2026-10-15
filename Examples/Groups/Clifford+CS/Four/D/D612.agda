{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D612 where

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
open import Examples.Groups.Clifford+CS.Four.D.D058 using (lem-pass-CCZ123-vs-CCZ023 ; lem-pass-CCZ123-vs-CS13 ; lem-pass-CCZ123-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D312 using (lem-pass-CCZ023-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D605 using (lem-pass-CZ12-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D606 using (lem-pass-CZ12-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D611 using (lem-T-CZ03-T-at1023 ; lem-pass-CZ13-vs-CS13 ; lem-pass-CZ13-vs-CSd13 ; lem-pass-Z1-vs-CS13 ; lem-pass-Z1-vs-CSd13)
-- pass [Z1 CZ12 CZ13 CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 526 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (run b65)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 3 2 (CS13 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS13) ▸
       at 2 2 (CS13 ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CS13) ▸
       at 1 2 (CS13 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS13) ▸
       at 0 2 (CS13 ∷ Z1 ∷ []) (lem-pass-Z1-vs-CS13) ▸
       at 4 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b1 = at 13 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b2 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b2 = at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX02 ∷ []) (win 3 0 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b3 = at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX02 ∷ []) (win 3 0 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b4 = at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b5 = at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b6 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ Sw01 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b6 = at 5 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 14 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b7 = at 15 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b8 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b8 = at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b9 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b9 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b10 = at 13 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b11 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b11 = at 7 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b12 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b12 = at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 12 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b13 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b13 = at 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸ done

  b14 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ Sw12 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b14 = at 6 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b15 = at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b16 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b16 = at 9 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b17 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b17 = at 13 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b18 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ Sw12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b19 = at 7 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b20 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b20 = at 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b21 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b21 = at 11 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b22 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b22 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b23 = at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b24 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b24 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b25 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Z1 ∷ CZ12 ∷ Toff102 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CCZ023 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b25 = at 12 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 3 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸ done

  b26 : Chain (CS13 ∷ Z1 ∷ CZ12 ∷ Toff102 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CCZ023 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b26 = at 4 3 (CCZ023 ∷ CZ13 ∷ []) (lem-T-CZ03-T-at1023) ▸
       at 2 2 (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) (win 3 0 complete₃ ((CZ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CZ • Swap ↑) • (CZ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Toff102 ∷ Z1 ∷ CZ02 ∷ []) (win 3 0 complete₃ ((Z ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Z ↑) • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CZ13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ13) ▸
       at 8 2 (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023) ▸
       at 3 2 [] (win 3 0 complete₃ ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b27 = at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b28 : Chain (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b28 = at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b29 : Chain (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b29 = at 9 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b30 = at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b31 : Chain (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b31 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b32 : Chain (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS13⁻ ∷ CCZ123 ∷ Toff102 ∷ [])
  b32 = at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 2 (CS13⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd13) ▸ done

  b33 : Chain (CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS13⁻ ∷ CCZ123 ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ K0 ∷ ι1 ∷ Sw01 ∷ [])
  b33 = at 4 2 (CS13⁻ ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CSd13) ▸
       at 3 2 (CS13⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd13) ▸
       at 2 2 (CS13⁻ ∷ Z1 ∷ []) (lem-pass-Z1-vs-CSd13) ▸
       at 6 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸ done

  b34 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw01 ∷ K0 ∷ ι1 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ [])
  b34 = at 14 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 10 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 10 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b35 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ [])
  b35 = at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX02 ∷ []) (win 3 0 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸ done

  b36 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ [])
  b36 = at 9 2 (Sw01 ∷ CX02 ∷ []) (win 3 0 complete₃ ((CX₀₁ ↑) • Swap) (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 13 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b37 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ [])
  b37 = at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 10 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw01 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ [])
  b38 = at 14 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸ done

  b39 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ [])
  b39 = at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 16 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b40 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ [])
  b40 = at 14 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 11 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b41 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ [])
  b41 = at 11 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ [])
  b42 = at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸ done

  b43 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ [])
  b43 = at 13 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b44 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ [])
  b44 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ [])
  b45 = at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 11 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 14 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b46 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ [])
  b46 = at 15 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b47 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ [])
  b47 = at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b48 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ [])
  b48 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b49 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ [])
  b49 = at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 15 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b50 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ [])
  b50 = at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b51 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ Sw12 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw01 ∷ [])
  b51 = at 14 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b52 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ Sw12 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ [])
  b52 = at 10 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸ done

  b53 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ [])
  b53 = at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b54 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ [])
  b54 = at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ [])
  b55 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b56 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ [])
  b56 = at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b57 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b57 = at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b58 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ Toff102 ∷ CCZ023 ∷ CZ13 ∷ CCZ123 ∷ CCZ023 ∷ [])
  b58 = at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 6 3 (CCZ023 ∷ CZ13 ∷ []) (lem-T-CZ03-T-at1023) ▸ done

  b59 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ Toff102 ∷ CCZ023 ∷ CZ13 ∷ CCZ123 ∷ CCZ023 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ [])
  b59 = at 4 2 (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) (win 3 0 complete₃ ((CZ ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CZ • Swap ↑) • (CZ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ Z1 ∷ CZ02 ∷ []) (win 3 0 complete₃ ((Z ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Z ↑) • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (CZ13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ13) ▸
       at 10 2 (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023) ▸
       at 5 2 [] (win 3 0 complete₃ ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b60 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ [])
  b60 = at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b61 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ [])
  b61 = at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸ done

  b62 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ [])
  b62 = at 10 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b63 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ [])
  b63 = at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b64 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ [])
  b64 = at 12 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸ done

  b65 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ [])
  b65 = at 8 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

