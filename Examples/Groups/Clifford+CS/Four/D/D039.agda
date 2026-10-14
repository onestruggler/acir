{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D039 where

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
open import Examples.Groups.Clifford+CS.Four.D.D025 using (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03)
-- pass [X3 CK30 X3] [TOFF012 CS03 TOFF012 CSd03]: 454 steps
lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (run b56))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ [])
  b0 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ [])
  b1 = at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ [])
  b2 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b3 : Chain (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b3 = at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b4 : Chain (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b4 = at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b5 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b6 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b7 = at 4 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b8 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b9 = at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 12 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ Sw12 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b10 = at 13 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ Sw12 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b11 = at 7 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸ done

  b12 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b12 = at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 15 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 8 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b13 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b13 = at 8 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b14 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b14 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b15 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b15 = at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 10 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b16 = at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS23 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸ done

  b17 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b17 = at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b18 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b18 = at 12 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 13 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b19 = at 3 2 (Sw12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸ done

  b20 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b20 = at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b21 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b21 = at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 15 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b22 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b22 = at 13 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 7 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸ done

  b23 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b23 = at 8 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 8 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS01 ∷ []) (win 3 0 complete₃ (CS • Swap) (Swap • CS) tt tt Eq.refl) ▸
       at 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b24 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b24 = at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸ done

  b25 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b25 = at 12 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b26 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw01 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b26 = at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) (Swap • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 2 (Sw01 ∷ K1 ∷ []) (win 3 0 complete₃ (K • Swap) (Swap • (K ↑)) tt tt Eq.refl) ▸
       at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (Sw23 ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw01 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b27 = at 4 2 (Sw01 ∷ X0 ∷ []) (win 3 0 complete₃ ((X ↑) • Swap) (Swap • X) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CK01 ∷ []) (win 3 0 complete₃ (CK₁₀ • Swap) (Swap • CK₀₁) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ X0 ∷ []) (win 3 0 complete₃ ((X ↑) • Swap) (Swap • X) tt tt Eq.refl) ▸
       at 3 6 (Toff123 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (ax ck-tct) ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b28 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b28 = at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸ done

  b29 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b29 = at 9 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b30 = at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 3 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸ done

  b31 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw01 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b31 = at 2 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CS) (CS • Swap) tt tt Eq.refl) ▸
       at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b32 : Chain (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b32 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b33 : Chain (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ Sw01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b33 = at 5 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸ done

  b34 : Chain (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw01 ∷ X0 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ X1 ∷ Sw01 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b34 = at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 12 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 5 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (win 0 3 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 5 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (X1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • X) ((X ↑) • Swap) tt tt Eq.refl) ▸ done

  b35 : Chain (Sw23 ∷ Sw12 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ X1 ∷ Sw01 ∷ CK01 ∷ X0 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b35 = at 6 2 (CK10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CK₀₁) (CK₁₀ • Swap) tt tt Eq.refl) ▸
       at 7 2 (X1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • X) ((X ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b36 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b36 = at 5 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸ done

  b37 : Chain (Sw23 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw01 ∷ ι1 ∷ Sw01 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b37 = at 9 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b38 : Chain (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS03 ∷ K0 ∷ ι ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b38 = at 5 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸ done

  b39 : Chain (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b39 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b40 : Chain (Sw23 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS01 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Toff013 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b40 = at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b41 : Chain (Sw23 ∷ Toff013 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ Toff023 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b41 = at 2 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b42 : Chain (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b42 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (K ↑)) (K • Swap) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 12 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b43 : Chain (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw12 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b43 = at 3 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 4 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b44 : Chain (Sw23 ∷ Toff013 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b44 = at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b45 : Chain (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b45 = at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b46 : Chain (Sw23 ∷ Toff013 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw12 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ Sw12 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b46 = at 10 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸ done

  b47 : Chain (Sw23 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ Sw12 ∷ X1 ∷ Sw12 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b47 = at 6 2 (X2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b48 : Chain (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ []) (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b48 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b49 : Chain (Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b49 = at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b50 : Chain (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02 ∷ Toff013 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b50 = at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 0 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b51 : Chain (Toff012 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b51 = at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b52 : Chain (Toff012 ∷ CS03 ∷ Sw23 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b52 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b53 : Chain (Toff012 ∷ CS03 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ [])
  b53 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸ done

  b54 : Chain (Toff012 ∷ CS03 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b54 = at 2 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 2 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b55 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ [])
  b55 = at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 4 4 (CS02⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b56 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b56 = at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X3 CKd30 X3] [TOFF012 CS03 TOFF012 CSd03]: 19 steps
lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ CK30⁻ ∷ X3 ∷ [])
  b0 = at 7 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (CK20 ∷ CK20⁻ ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ CK30⁻ ∷ X3 ∷ []) (X3 ∷ Sw23 ∷ CK20⁻ ∷ CK20 ∷ Sw23 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b1 = at 9 0 (X3 ∷ X3 ∷ []) (win 0 3 complete₃ (ε) ((X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 7 (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (X3 ∷ Sw23 ∷ CK20⁻ ∷ CK20 ∷ Sw23 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b2 = at 2 2 [] (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd03] [TOFF012 CS03 TOFF012 CSd03]: 1 steps
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ [])
  b0 = at 0 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03) ▸ done

