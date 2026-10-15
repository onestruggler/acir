{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D103 where

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

-- sw2 Sd0: 2 steps
lem-sw2-Sd0 : ⟪ (Sw23 ∷ S0⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw2-Sd0 = run b0
  where
  b0 : Chain (Sw23 ∷ S0⁻ ∷ Sw23 ∷ []) (S0⁻ ∷ [])
  b0 = at 0 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 K0: 2 steps
lem-sw2-K0 : ⟪ (Sw23 ∷ K0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw2-K0 = run b0
  where
  b0 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ []) (K0 ∷ [])
  b0 = at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Kd0: 2 steps
lem-sw2-Kd0 : ⟪ (Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw2-Kd0 = run b0
  where
  b0 : Chain (Sw23 ∷ K0⁻ ∷ Sw23 ∷ []) (K0⁻ ∷ [])
  b0 = at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 X0: 2 steps
lem-sw2-X0 : ⟪ (Sw23 ∷ X0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw2-X0 = run b0
  where
  b0 : Chain (Sw23 ∷ X0 ∷ Sw23 ∷ []) (X0 ∷ [])
  b0 = at 0 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Z0: 2 steps
lem-sw2-Z0 : ⟪ (Sw23 ∷ Z0 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw2-Z0 = run b0
  where
  b0 : Chain (Sw23 ∷ Z0 ∷ Sw23 ∷ []) (Z0 ∷ [])
  b0 = at 0 2 (Z0 ∷ Sw23 ∷ []) (sym (low₁-comm (Z) ((Swap ↑)))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 S1: 2 steps
lem-sw2-S1 : ⟪ (Sw23 ∷ S1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw2-S1 = run b0
  where
  b0 : Chain (Sw23 ∷ S1 ∷ Sw23 ∷ []) (S1 ∷ [])
  b0 = at 0 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Sd1: 2 steps
lem-sw2-Sd1 : ⟪ (Sw23 ∷ S1⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw2-Sd1 = run b0
  where
  b0 : Chain (Sw23 ∷ S1⁻ ∷ Sw23 ∷ []) (S1⁻ ∷ [])
  b0 = at 0 2 (S1⁻ ∷ Sw23 ∷ []) (sym (low-comm (((S • S • S) ↑)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 K1: 2 steps
lem-sw2-K1 : ⟪ (Sw23 ∷ K1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw2-K1 = run b0
  where
  b0 : Chain (Sw23 ∷ K1 ∷ Sw23 ∷ []) (K1 ∷ [])
  b0 = at 0 2 (K1 ∷ Sw23 ∷ []) (sym (low-comm ((K ↑)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Kd1: 2 steps
lem-sw2-Kd1 : ⟪ (Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw2-Kd1 = run b0
  where
  b0 : Chain (Sw23 ∷ K1⁻ ∷ Sw23 ∷ []) (K1⁻ ∷ [])
  b0 = at 0 2 (K1⁻ ∷ Sw23 ∷ []) (sym (low-comm (((K • iI) ↑)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 X1: 2 steps
lem-sw2-X1 : ⟪ (Sw23 ∷ X1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw2-X1 = run b0
  where
  b0 : Chain (Sw23 ∷ X1 ∷ Sw23 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Z1: 2 steps
lem-sw2-Z1 : ⟪ (Sw23 ∷ Z1 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw2-Z1 = run b0
  where
  b0 : Chain (Sw23 ∷ Z1 ∷ Sw23 ∷ []) (Z1 ∷ [])
  b0 = at 0 2 (Z1 ∷ Sw23 ∷ []) (sym (low-comm ((Z ↑)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 S2: 2 steps
lem-sw2-S2 : ⟪ (Sw23 ∷ S2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw2-S2 = run b0
  where
  b0 : Chain (Sw23 ∷ S2 ∷ Sw23 ∷ []) (S3 ∷ [])
  b0 = at 0 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Sd2: 2 steps
lem-sw2-Sd2 : ⟪ (Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw2-Sd2 = run b0
  where
  b0 : Chain (Sw23 ∷ S2⁻ ∷ Sw23 ∷ []) (S3⁻ ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 K2: 2 steps
lem-sw2-K2 : ⟪ (Sw23 ∷ K2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw2-K2 = run b0
  where
  b0 : Chain (Sw23 ∷ K2 ∷ Sw23 ∷ []) (K3 ∷ [])
  b0 = at 0 2 (K3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑)) ((K ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Kd2: 2 steps
lem-sw2-Kd2 : ⟪ (Sw23 ∷ K2⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw2-Kd2 = run b0
  where
  b0 : Chain (Sw23 ∷ K2⁻ ∷ Sw23 ∷ []) (K3⁻ ∷ [])
  b0 = at 0 2 (K3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((K • iI) ↑)) (((K • iI) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 X2: 2 steps
lem-sw2-X2 : ⟪ (Sw23 ∷ X2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw2-X2 = run b0
  where
  b0 : Chain (Sw23 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ [])
  b0 = at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

