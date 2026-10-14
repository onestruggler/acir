{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D048 where

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


-- SW13-Rk: 743 steps (scratchpad/four/lower.py)
lem-SW13-Rk : ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-SW13-Rk = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (trans (run b65) (trans (run b66) (trans (run b67) (trans (run b68) (trans (run b69) (trans (run b70) (trans (run b71) (trans (run b72) (trans (run b73) (trans (run b74) (trans (run b75) (trans (run b76) (trans (run b77) (trans (run b78) (trans (run b79) (trans (run b80) (trans (run b81) (trans (run b82) (trans (run b83) (trans (run b84) (trans (run b85) (trans (run b86) (trans (run b87) (trans (run b88) (trans (run b89) (trans (run b90) (trans (run b91) (run b92))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 13 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b1 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b1 = at 14 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 16 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b2 = at 18 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 19 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 20 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 19 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 18 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 18 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b3 = at 17 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 14 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 12 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸
       at 13 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b4 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b4 = at 13 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (win 0 3 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 14 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 14 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 16 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b5 = at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 14 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 15 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b6 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b6 = at 16 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 17 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 19 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b7 = at 14 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 13 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K0⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((K • iI) ↑)) ((K • iI) • Swap) tt tt Eq.refl) ▸
       at 15 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 14 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap)) ▸
       at 15 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CCZ023 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b8 = at 16 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 15 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 16 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 16 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 17 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 18 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b9 = at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 20 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 21 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 19 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 20 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b10 = at 19 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 20 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 17 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 16 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 16 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 16 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b11 = at 16 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 15 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 17 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 18 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 16 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ CX31 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b12 = at 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 19 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 20 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 16 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ Sw12 ∷ Sw12 ∷ CS02⁻ ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS13 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b13 = at 19 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 22 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 3 (CS13 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑) • Swap) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 24 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 24 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b14 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ Sw12 ∷ Sw12 ∷ CS02⁻ ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CS13 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b14 = at 25 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 20 3 (CS01⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑)) ((CS • CS • CS)) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 18 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 19 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS01 ∷ CX30 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b15 = at 17 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 3 (CS01 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) tt tt Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸ done

  b16 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS01 ∷ CX30 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b16 = at 15 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 15 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 15 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b17 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b17 = at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b18 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ [])
  b18 = at 16 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b19 = at 14 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 11 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 12 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b20 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b20 = at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b21 = at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b22 = at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 13 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 12 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸
       at 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b23 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b23 = at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b24 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b24 = at 18 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b25 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b25 = at 16 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 19 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 12 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 11 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ Sw12 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b26 = at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 3 (CK20⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b27 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b27 = at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸ done

  b28 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b28 = at 13 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 14 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b29 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b29 = at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸
       at 7 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b30 = at 7 1 (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (win 0 3 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b31 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b31 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b32 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b32 = at 11 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b33 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ K1⁻ ∷ Sw01 ∷ Sw12 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b33 = at 7 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((K • iI) ↑)) ((K • iI) • Swap) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap)) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b34 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CCZ023 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b34 = at 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b35 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b35 = at 14 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b36 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b36 = at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 10 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 10 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸ done

  b37 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b37 = at 9 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CS23 ∷ Sw01 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ Sw12 ∷ Sw12 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b38 = at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 14 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b39 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ Sw12 ∷ Sw12 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Sw12 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ Sw12 ∷ Sw12 ∷ CS02⁻ ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ CS13 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b39 = at 16 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 3 (CS13 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑) • Swap) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 18 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 19 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done

  b40 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ Sw12 ∷ Sw12 ∷ CS02⁻ ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ CX30 ∷ CS13 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b40 = at 17 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 3 (CS01⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑)) ((CS • CS • CS)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 12 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b41 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ Sw12 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b41 = at 8 3 (CS01 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) tt tt Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b42 = at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 9 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b43 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b43 = at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b44 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b44 = at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ CCZ013 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b45 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 5 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b46 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b46 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b47 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b47 = at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b48 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b48 = at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b49 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b49 = at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b50 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b50 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b51 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff013 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ [])
  b51 = at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b52 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff013 ∷ CK20⁻ ∷ Toff013 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b52 = at 2 3 (CK20 ∷ []) (win 3 0 complete₃ ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b53 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b53 = at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b54 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b54 = at 17 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 18 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 17 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b55 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b55 = at 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 12 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 12 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b56 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b56 = at 12 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b57 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b57 = at 15 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b58 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ [])
  b58 = at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 13 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸ done

  b59 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ [])
  b59 = at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸ done

  b60 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ [])
  b60 = at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b61 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ [])
  b61 = at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b62 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ [])
  b62 = at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 15 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 15 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 14 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸ done

  b63 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS13 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ [])
  b63 = at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b64 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ CS13 ∷ Sw23 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ K0⁻ ∷ Sw12 ∷ [])
  b64 = at 24 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 3 (CS12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) tt tt Eq.refl) ▸
       at 25 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 24 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 23 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 24 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 23 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b65 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ Sw12 ∷ [])
  b65 = at 24 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 23 3 (CX21 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸
       at 22 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 23 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 19 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b66 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw01 ∷ CX21 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ Sw12 ∷ [])
  b66 = at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 18 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 17 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 18 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 3 (CX21 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸ done

  b67 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw01 ∷ CX21 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ [])
  b67 = at 16 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 17 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸ done

  b68 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ [])
  b68 = at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CK31⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑ • CK₁₀) • (Swap ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b69 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ CK20⁻ ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b69 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b70 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b70 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b71 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b71 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b72 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b72 = at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸ done

  b73 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b73 = at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b74 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b74 = at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b75 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ Sw23 ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b75 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b76 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CCZ013 ∷ K0⁻ ∷ Sw23 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b76 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b77 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b77 = at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b78 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b78 = at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b79 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b79 = at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b80 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b80 = at 11 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b81 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw23 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b81 = at 19 3 (CS12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑)) (CS) tt tt Eq.refl) ▸
       at 19 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 18 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 17 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 18 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸ done

  b82 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CS01⁻ ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ CX31 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b82 = at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 3 (CX21 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸
       at 16 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 17 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b83 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b83 = at 11 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CX21 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸
       at 10 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b84 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS01 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw01 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b84 = at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 5 (CCZ012 ∷ []) (win 3 0 complete₃ (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b85 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ [])
  b85 = at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31 ∷ []) (win 0 3 complete₃ ((Swap ↑) • CK₁₀ • (Swap ↑)) ((Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b86 : Chain (Sw12 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CK30⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ [])
  b86 = at 1 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap)) ▸ done

  b87 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CK30⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ []) (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CK30⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ CS12 ∷ K0⁻ ∷ [])
  b87 = at 13 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 14 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 23 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 24 3 (CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑) • (Swap ↑)) ((CS ↑)) tt tt Eq.refl) ▸ done

  b88 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CK30⁻ ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ CS12 ∷ K0⁻ ∷ []) (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CK30⁻ ∷ Sw12 ∷ Toff012 ∷ [])
  b88 = at 21 3 (CX10 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸
       at 18 3 (CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS • CS • CS) • (Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CX10 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸
       at 12 3 (CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑) • CS • (Swap ↑)) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 12 5 (CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 10 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 9 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸ done

  b89 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ CK30⁻ ∷ Sw12 ∷ Toff012 ∷ []) (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ Sw12 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b89 = at 7 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 7 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (Toff) (K • CCZ • (K • iI)) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b90 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ CCZ012 ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ Sw12 ∷ CK30⁻ ∷ Toff012 ∷ []) (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ CS12 ∷ Sw12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ [])
  b90 = at 8 2 (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap)) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (win 3 0 complete₃ (CCZ) (CS • (Swap ↑ • CX₁₀ • Swap ↑) • (CS • CS • CS) • (Swap ↑ • CX₁₀ • Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b91 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ Sw12 ∷ K0 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw12 ∷ CX20 ∷ Sw12 ∷ Sw12 ∷ CS12 ∷ Sw12 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ []) (Sw12 ∷ CK30 ∷ Sw12 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ [])
  b91 = at 18 3 (CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑) • (Swap ↑)) ((CS ↑)) tt tt Eq.refl) ▸
       at 15 3 (CX10 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸
       at 12 3 (CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS • CS • CS) • (Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX10 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑)) (CX₁₀) tt tt Eq.refl) ▸
       at 6 3 (CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑) • CS • (Swap ↑)) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑)) (CCZ) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 3 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b92 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ K0 ∷ CCZ012 ∷ K0⁻ ∷ CK30⁻ ∷ Toff012 ∷ []) (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ [])
  b92 = at 3 3 (Toff012 ∷ []) (win 3 0 complete₃ (K • CCZ • (K • iI)) (Toff) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 1 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

