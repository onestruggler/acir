{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D783 where

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
open import Examples.Groups.Clifford+CS.Four.D.D045 using (lem-merge-R0)
-- merge R0 @3012: 335 steps
lem-merge-R0-at3012 : ⟪ (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) ⟫ʷ
lem-merge-R0-at3012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (run b41)))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b0 = at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 2 (Sw23 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑)) ((Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw23 ∷ K2⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b1 = at 15 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b2 = at 21 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 22 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 21 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 20 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b3 = at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 15 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 15 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b4 = at 12 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b5 = at 16 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 19 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 18 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸ done

  b6 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ K3 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b6 = at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b7 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X2 ∷ S3 ∷ K3 ∷ CS23 ∷ K3 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ Sw23 ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b7 = at 12 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 13 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 13 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑)) ((Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ Sw23 ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b8 = at 6 2 (Sw23 ∷ K2⁻ ∷ []) (win 0 3 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b9 = at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b10 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ Sw23 ∷ ι ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b10 = at 11 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ K3 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ K3 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b11 = at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 6 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ CS23⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b12 : Chain (S3 ∷ K3 ∷ CS23 ∷ K3 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b12 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw23 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b13 = at 9 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b14 : Chain (S3 ∷ K3 ∷ CS23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (S3 ∷ K3 ∷ CS23 ∷ Sw23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ [])
  b14 = at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 4 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (S3 ∷ K3 ∷ CS23 ∷ Sw23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b15 = at 2 2 (Sw23 ∷ CS23 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ K2 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 19 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 2 (Sw12 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑)) (X))) ▸
       at 17 2 (Sw12 ∷ S1⁻ ∷ []) (win 3 0 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw12 ∷ K1⁻ ∷ []) (win 3 0 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 15 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw12 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b16 = at 22 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 21 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 19 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 17 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b17 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw12 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b17 = at 18 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 16 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 16 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 13 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸ done

  b18 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw12 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b18 = at 19 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 15 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ X3 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ Sw12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ Sw12 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b19 = at 14 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 14 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 14 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw12 ∷ S1 ∷ []) (win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw12 ∷ X3 ∷ []) (sym (low₃-comm ((Swap ↑)) (X))) ▸ done

  b20 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ K2⁻ ∷ S2⁻ ∷ Sw12 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b20 = at 8 2 (Sw12 ∷ S1⁻ ∷ []) (win 3 0 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw12 ∷ K1⁻ ∷ []) (win 3 0 complete₃ (((K • iI) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((K • iI) ↑)) tt tt Eq.refl) ▸
       at 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 12 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b21 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS01 ∷ K1 ∷ ι ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw12 ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b21 = at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 7 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 7 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Sw12 ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b22 = at 5 2 (Sw12 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 10 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (Sw23 ∷ S2 ∷ K2 ∷ CS23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ K2 ∷ Sw12 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ [])
  b23 = at 7 2 (Sw12 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (Swap ↑)) ((Swap ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw12 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑)) ((Swap ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 5 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑) • iI) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b24 : Chain (Sw23 ∷ S2 ∷ K2 ∷ Sw12 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b24 = at 2 2 (Sw12 ∷ K1 ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (Swap ↑)) ((Swap ↑) • (K ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw12 ∷ S1 ∷ []) (win 3 0 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 20 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 19 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 18 2 (Sw01 ∷ S0⁻ ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • Swap) (Swap • (S • S • S)) tt tt Eq.refl) ▸
       at 17 2 (Sw01 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (((K • iI) ↑) • Swap) (Swap • (K • iI)) tt tt Eq.refl) ▸
       at 16 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸ done

  b25 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b25 = at 22 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 21 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 20 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 19 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 18 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 17 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 17 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b26 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b26 = at 17 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 16 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 16 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸ done

  b27 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw01 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b27 = at 20 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 19 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 18 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 17 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 16 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 15 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 15 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸ done

  b28 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b28 = at 15 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ S0 ∷ []) (win 3 0 complete₃ ((S ↑) • Swap) (Swap • S) tt tt Eq.refl) ▸ done

  b29 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Sw01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b29 = at 10 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 2 (Sw01 ∷ S0⁻ ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • Swap) (Swap • (S • S • S)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (((K • iI) ↑) • Swap) (Swap • (K • iI)) tt tt Eq.refl) ▸
       at 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 12 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸ done

  b30 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b30 = at 10 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b31 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b31 = at 7 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸ done

  b32 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ CS13 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b32 = at 8 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b33 : Chain (Sw23 ∷ Sw12 ∷ S1 ∷ K1 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ CS02⁻ ∷ S1 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b33 = at 5 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ S0 ∷ []) (win 3 0 complete₃ ((S ↑) • Swap) (Swap • S) tt tt Eq.refl) ▸
       at 3 18 (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (lem-merge-R0) ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (S1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • S) ((S ↑) • Swap) tt tt Eq.refl) ▸ done

  b34 : Chain (Sw23 ∷ Sw12 ∷ CS02⁻ ∷ S1 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ CS02⁻ ∷ S1 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ Sw01 ∷ ι ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b34 = at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (K1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • K) ((K ↑) • Swap) tt tt Eq.refl) ▸ done

  b35 : Chain (Sw23 ∷ Sw12 ∷ CS02⁻ ∷ S1 ∷ K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ Sw01 ∷ ι ∷ S0⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ S2 ∷ Sw12 ∷ Toff102 ∷ S1⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b35 = at 11 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 4 8 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑) • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • (K ↑) • (iI ↑)) ((K ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑) • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (S1⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (S • S • S)) (((S • S • S) ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (S2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b36 : Chain (Sw23 ∷ CS01⁻ ∷ S2 ∷ Sw12 ∷ Toff102 ∷ S1⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ S2 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K1 ∷ ι ∷ S1⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b36 = at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (CS12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b37 : Chain (Sw23 ∷ CS01⁻ ∷ S2 ∷ K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ CS02 ∷ K1 ∷ ι ∷ S1⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ Sw23 ∷ [])
  b37 = at 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (K2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (S2⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b38 : Chain (Sw23 ∷ CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ Sw23 ∷ []) (CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ Sw23 ∷ [])
  b38 = at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 1 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b39 : Chain (CS01⁻ ∷ S3 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ S2⁻ ∷ Sw23 ∷ []) (CS01⁻ ∷ S3 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ Sw23 ∷ [])
  b39 = at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b40 : Chain (CS01⁻ ∷ S3 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) (CS01⁻ ∷ S3 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ Sw23 ∷ [])
  b40 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b41 : Chain (CS01⁻ ∷ S3 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ [])
  b41 = at 9 2 (K2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 8 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (win 3 0 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

