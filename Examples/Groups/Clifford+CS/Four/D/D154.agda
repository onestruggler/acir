{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D154 where

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

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02] part0: 500 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0 : ⟪ (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ X1 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b0 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ X1 ∷ X3 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ X1 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b2 : Chain (CS03 ∷ X1 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ X1 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b2 = at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ X1 ∷ X3 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b3 = at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b4 : Chain (CS03 ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b4 = at 2 5 (X0 ∷ CX10 ∷ CX20 ∷ Toff012 ∷ []) (win 3 0 complete₃ ((X ↑) • (X ↑ ↑) • Toff • (X ↑) • (X ↑ ↑)) (X • CX₁₀ • (Swap ↑ • CX₁₀ • Swap ↑) • Toff) tt tt Eq.refl) ▸
       at 1 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 2 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b5 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b6 : Chain (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b6 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b7 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (CS03 ∷ X0 ∷ CX10 ∷ CX30 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ S3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b8 = at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (X0 ∷ S2 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • X) (X • (S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 1 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (X0 ∷ S3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ CX10 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ S3 ∷ Sw23 ∷ CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b9 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀) (CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • ((CS • CS • CS) ↑) • CCZ) tt tt Eq.refl) ▸ done

  b10 : Chain (X0 ∷ S3 ∷ Sw23 ∷ CX10 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ S3 ∷ CX10 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b10 = at 2 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (X0 ∷ S3 ∷ CX10 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ S3 ∷ CX10 ∷ CS03⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b11 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (X0 ∷ S3 ∷ CX10 ∷ CS03⁻ ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ S3 ∷ CX10 ∷ CS03⁻ ∷ CS13⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b12 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b13 : Chain (X0 ∷ S3 ∷ CX10 ∷ CS03⁻ ∷ CS13⁻ ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX30 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b13 = at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CX10 ∷ S3 ∷ []) (sym (low-comm (CX₁₀) ((S ↑)))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b14 = at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b15 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX20 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b15 = at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b16 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CX20 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b16 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX20 ∷ CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b17 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b17 = at 6 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b18 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b18 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b19 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b19 = at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 8 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b20 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CS13⁻ ∷ CX30 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CX30 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b20 = at 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX20 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b21 : Chain (X0 ∷ CX10 ∷ S3 ∷ CS03⁻ ∷ CX30 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ Sw23 ∷ CX20 ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b21 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX20 ∷ S2⁻ ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b22 : Chain (X0 ∷ CX10 ∷ S3 ∷ Sw23 ∷ CX20 ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ S3 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b22 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (S3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (X0 ∷ CX10 ∷ S3 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b23 = at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 3 2 (CX20 ∷ S2 ∷ []) (win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b24 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b24 = at 9 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b25 = at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 16 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 15 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b26 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b26 = at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b27 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CCZ013 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b27 = at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 10 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 10 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b28 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b28 = at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b29 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Toff012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b29 = at 11 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b30 = at 9 2 (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • Toff) (Toff • (CZ ↑) • CCZ) tt tt Eq.refl) ▸
       at 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b31 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b31 = at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b32 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b32 = at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b33 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b33 = at 16 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b34 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b34 = at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b35 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b35 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b36 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b36 = at 11 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 11 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b37 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b37 = at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b38 = at 14 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 14 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b39 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b39 = at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b40 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CZ12 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b40 = at 7 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Toff012 ∷ CZ12 ∷ []) (win 3 0 complete₃ ((CZ ↑) • Toff) (Toff • (CZ ↑)) tt tt Eq.refl) ▸
       at 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b41 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CZ12 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b41 = at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b42 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b42 = at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b43 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b43 = at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b44 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ Toff013 ∷ CZ13 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b44 = at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b45 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b45 = at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b46 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b46 = at 14 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 13 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b47 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ Toff012 ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b47 = at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Toff012 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Toff) (Toff • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done

  b48 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ Toff012 ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b48 = at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b49 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b49 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b50 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b50 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b51 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b51 = at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b52 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b52 = at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b53 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b53 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 12 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b54 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b54 = at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸ done

  b55 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b55 = at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Toff) (Toff • (Swap ↑ • CS • Swap ↑) • (CS ↑) • CCZ) tt tt Eq.refl) ▸
       at 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b56 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b56 = at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b57 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b57 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b58 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ Sw23 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b58 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b59 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ Sw23 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b59 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b60 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ CS03 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b60 = at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b61 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ CS03 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ CS03 ∷ CS13 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b61 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 9 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b62 : Chain (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Toff013 ∷ CS03 ∷ CS13 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ [])
  b62 = at 8 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

