{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D049 where

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


-- PU: 117 steps (scratchpad/four/lower.py)
lem-PU : ⟪ (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-PU = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b0 = at 6 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (win 3 0 complete₃ (ε) ((K • iI) • (S • S • S) • K • (K • iI) • S • K) tt tt Eq.refl) ▸
       at 5 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (win 3 0 complete₃ (ε) ((K • iI) • (S • S • S) • K • (K • iI) • S • K) tt tt Eq.refl) ▸
       at 4 0 (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (win 3 0 complete₃ (ε) ((K • iI) • (S • S • S) • K • (K • iI) • S • K) tt tt Eq.refl) ▸
       at 0 7 (Toff012 ∷ []) (win 3 0 complete₃ ((K • iI) • S • K • Toff • (K • iI) • (S • S • S) • K) (Toff) tt tt Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸ done

  b1 : Chain (Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ CK30 ∷ Sw23 ∷ CX20 ∷ S2 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ [])
  b1 = at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 2 7 (CK20 ∷ CX20 ∷ S2 ∷ []) (win 3 0 complete₃ ((K • iI) • S • K • (Swap ↑ • CS • Swap ↑) • (K • iI) • (S • S • S) • K) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CK30 ∷ Sw23 ∷ CX20 ∷ S2 ∷ Sw23 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ []) (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ Sw23 ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ [])
  b2 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 7 (Toff012 ∷ []) (win 3 0 complete₃ ((K • iI) • S • K • Toff • (K • iI) • (S • S • S) • K) (Toff) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 10 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸ done

  b3 : Chain (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ Sw23 ∷ S0⁻ ∷ K0 ∷ Sw23 ∷ []) (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ S3⁻ ∷ Sw23 ∷ CX20 ∷ CK20⁻ ∷ Sw23 ∷ [])
  b3 = at 9 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 6 7 (S2⁻ ∷ CX20 ∷ CK20⁻ ∷ []) (win 3 0 complete₃ ((K • iI) • S • K • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (K • iI) • (S • S • S) • K) (((S • S • S) ↑ ↑) • (Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 (S3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (Toff012 ∷ CK30 ∷ CX30 ∷ S3 ∷ Toff012 ∷ S3⁻ ∷ Sw23 ∷ CX20 ∷ CK20⁻ ∷ Sw23 ∷ []) (Toff012 ∷ CK30 ∷ CX30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b4 = at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Toff012 ∷ S3 ∷ []) (sym (low₃-comm (Toff) (S))) ▸
       at 4 2 [] (win 0 3 complete₃ ((S ↑ ↑) • ((S • S • S) ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 3 1 (CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ []) (win 3 0 complete₃ (Toff) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) tt tt Eq.refl) ▸ done

  b5 : Chain (Toff012 ∷ CK30 ∷ CX30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b5 = at 6 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b6 : Chain (Toff012 ∷ CK30 ∷ Sw01 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ CK21⁻ ∷ CS12 ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b6 = at 3 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 3 4 (CK21⁻ ∷ CS12 ∷ CK21 ∷ CX31 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b7 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ CX20 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b7 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁)) ▸ done

  b8 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CX30 ∷ Sw01 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b8 = at 6 2 (CX13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CX30 ∷ Sw01 ∷ CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CK21 ∷ CX31 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b9 = at 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CX21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) (Swap • (CX₁₀ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 7 4 (CK21⁻ ∷ CS12⁻ ∷ CK21 ∷ CX31 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀) ((S ↑ • CK₁₀) • (CS • CS • CS) • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b10 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ Sw01 ∷ CK21 ∷ CX31 ∷ Sw01 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b10 = at 8 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CX30 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ [])
  b11 = at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁)) ▸
       at 10 2 (CX13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CX30 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ Sw23 ∷ CS01 ∷ CK10 ∷ CX20 ∷ Sw23 ∷ CX30 ∷ CK30⁻ ∷ [])
  b12 = at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 12 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 11 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 10 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 4 (CK10⁻ ∷ CS01 ∷ CK10 ∷ CX20 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) ((S ↑ • CK₁₀) • CS • CK₁₀ • (Swap ↑ • CX₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸ done

  b13 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ Sw23 ∷ CS01 ∷ CK10 ∷ CX20 ∷ Sw23 ∷ CX30 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CK30⁻ ∷ [])
  b13 = at 11 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 12 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b14 : Chain (Toff012 ∷ CK30 ∷ CK20⁻ ∷ CS02 ∷ CK20 ∷ CX12 ∷ CK20⁻ ∷ CS02⁻ ∷ CK20 ∷ CX12 ∷ CK10⁻ ∷ CS01 ∷ CK10 ∷ CX30 ∷ Sw23 ∷ CX20 ∷ Sw23 ∷ CK30⁻ ∷ []) (Toff012 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ [])
  b14 = at 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 [] (win 3 0 complete₃ ((Swap ↑ • CX₁₀ • Swap ↑) • (Swap ↑ • CX₁₀ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 11 (Toff012 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (CX₀₁ ↑) • (S ↑ • CK₁₀) • CS • CK₁₀) (Toff) tt tt Eq.refl) ▸ done

