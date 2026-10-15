{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D097 where

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

-- sw0 TOFF312: 30 steps
lem-sw0-TOFF312 : ⟪ (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-sw0-TOFF312 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ [])
  b0 = at 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ K3 ∷ ι1 ∷ Sw01 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 7 2 (ι ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (iI ↑)) (iI • Swap) tt tt Eq.refl) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 2 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b2 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Sw01 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ K3 ∷ ι ∷ Sw01 ∷ Sw01 ∷ []) (Toff302 ∷ [])
  b3 = at 7 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 8 2 (ι1 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • iI) ((iI ↑) • Swap) tt tt Eq.refl) ▸
       at 1 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (win 0 3 complete₃ ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) ((K ↑ ↑) • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • (K ↑ ↑) • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw1 S0: 2 steps
lem-sw1-S0 : ⟪ (Sw12 ∷ S0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
lem-sw1-S0 = run b0
  where
  b0 : Chain (Sw12 ∷ S0 ∷ Sw12 ∷ []) (S0 ∷ [])
  b0 = at 0 2 (S0 ∷ Sw12 ∷ []) (sym (low₁-comm (S) (Swap))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Sd0: 2 steps
lem-sw1-Sd0 : ⟪ (Sw12 ∷ S0⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw1-Sd0 = run b0
  where
  b0 : Chain (Sw12 ∷ S0⁻ ∷ Sw12 ∷ []) (S0⁻ ∷ [])
  b0 = at 0 2 (S0⁻ ∷ Sw12 ∷ []) (sym (low₁-comm ((S • S • S)) (Swap))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 K0: 2 steps
lem-sw1-K0 : ⟪ (Sw12 ∷ K0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw1-K0 = run b0
  where
  b0 : Chain (Sw12 ∷ K0 ∷ Sw12 ∷ []) (K0 ∷ [])
  b0 = at 0 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Kd0: 2 steps
lem-sw1-Kd0 : ⟪ (Sw12 ∷ K0⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw1-Kd0 = run b0
  where
  b0 : Chain (Sw12 ∷ K0⁻ ∷ Sw12 ∷ []) (K0⁻ ∷ [])
  b0 = at 0 2 (K0⁻ ∷ Sw12 ∷ []) (sym (low₁-comm ((K • iI)) (Swap))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 X0: 2 steps
lem-sw1-X0 : ⟪ (Sw12 ∷ X0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw1-X0 = run b0
  where
  b0 : Chain (Sw12 ∷ X0 ∷ Sw12 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ Sw12 ∷ []) (sym (low₁-comm (X) (Swap))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Z0: 2 steps
lem-sw1-Z0 : ⟪ (Sw12 ∷ Z0 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw1-Z0 = run b0
  where
  b0 : Chain (Sw12 ∷ Z0 ∷ Sw12 ∷ []) (Z0 ∷ [])
  b0 = at 0 2 (Z0 ∷ Sw12 ∷ []) (sym (low₁-comm (Z) (Swap))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 S1: 2 steps
lem-sw1-S1 : ⟪ (Sw12 ∷ S1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw1-S1 = run b0
  where
  b0 : Chain (Sw12 ∷ S1 ∷ Sw12 ∷ []) (S2 ∷ [])
  b0 = at 0 2 (S2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Sd1: 2 steps
lem-sw1-Sd1 : ⟪ (Sw12 ∷ S1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw1-Sd1 = run b0
  where
  b0 : Chain (Sw12 ∷ S1⁻ ∷ Sw12 ∷ []) (S2⁻ ∷ [])
  b0 = at 0 2 (S2⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 K1: 2 steps
lem-sw1-K1 : ⟪ (Sw12 ∷ K1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw1-K1 = run b0
  where
  b0 : Chain (Sw12 ∷ K1 ∷ Sw12 ∷ []) (K2 ∷ [])
  b0 = at 0 2 (K2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Kd1: 2 steps
lem-sw1-Kd1 : ⟪ (Sw12 ∷ K1⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw1-Kd1 = run b0
  where
  b0 : Chain (Sw12 ∷ K1⁻ ∷ Sw12 ∷ []) (K2⁻ ∷ [])
  b0 = at 0 2 (K2⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 X1: 2 steps
lem-sw1-X1 : ⟪ (Sw12 ∷ X1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw1-X1 = run b0
  where
  b0 : Chain (Sw12 ∷ X1 ∷ Sw12 ∷ []) (X2 ∷ [])
  b0 = at 0 2 (X2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Z1: 2 steps
lem-sw1-Z1 : ⟪ (Sw12 ∷ Z1 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw1-Z1 = run b0
  where
  b0 : Chain (Sw12 ∷ Z1 ∷ Sw12 ∷ []) (Z2 ∷ [])
  b0 = at 0 2 (Z2 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 S2: 2 steps
lem-sw1-S2 : ⟪ (Sw12 ∷ S2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw1-S2 = run b0
  where
  b0 : Chain (Sw12 ∷ S2 ∷ Sw12 ∷ []) (S1 ∷ [])
  b0 = at 0 2 (S1 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Sd2: 2 steps
lem-sw1-Sd2 : ⟪ (Sw12 ∷ S2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw1-Sd2 = run b0
  where
  b0 : Chain (Sw12 ∷ S2⁻ ∷ Sw12 ∷ []) (S1⁻ ∷ [])
  b0 = at 0 2 (S1⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 K2: 2 steps
lem-sw1-K2 : ⟪ (Sw12 ∷ K2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw1-K2 = run b0
  where
  b0 : Chain (Sw12 ∷ K2 ∷ Sw12 ∷ []) (K1 ∷ [])
  b0 = at 0 2 (K1 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

