{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D098 where

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

-- sw1 Kd2: 2 steps
lem-sw1-Kd2 : ⟪ (Sw12 ∷ K2⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw1-Kd2 = run b0
  where
  b0 : Chain (Sw12 ∷ K2⁻ ∷ Sw12 ∷ []) (K1⁻ ∷ [])
  b0 = at 0 2 (K1⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 X2: 2 steps
lem-sw1-X2 : ⟪ (Sw12 ∷ X2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw1-X2 = run b0
  where
  b0 : Chain (Sw12 ∷ X2 ∷ Sw12 ∷ []) (X1 ∷ [])
  b0 = at 0 2 (X1 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Z2: 2 steps
lem-sw1-Z2 : ⟪ (Sw12 ∷ Z2 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw1-Z2 = run b0
  where
  b0 : Chain (Sw12 ∷ Z2 ∷ Sw12 ∷ []) (Z1 ∷ [])
  b0 = at 0 2 (Z1 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 S3: 2 steps
lem-sw1-S3 : ⟪ (Sw12 ∷ S3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw1-S3 = run b0
  where
  b0 : Chain (Sw12 ∷ S3 ∷ Sw12 ∷ []) (S3 ∷ [])
  b0 = at 0 2 (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S)) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Sd3: 2 steps
lem-sw1-Sd3 : ⟪ (Sw12 ∷ S3⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw1-Sd3 = run b0
  where
  b0 : Chain (Sw12 ∷ S3⁻ ∷ Sw12 ∷ []) (S3⁻ ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) ((S • S • S))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 K3: 2 steps
lem-sw1-K3 : ⟪ (Sw12 ∷ K3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw1-K3 = run b0
  where
  b0 : Chain (Sw12 ∷ K3 ∷ Sw12 ∷ []) (K3 ∷ [])
  b0 = at 0 2 (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K)) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Kd3: 2 steps
lem-sw1-Kd3 : ⟪ (Sw12 ∷ K3⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw1-Kd3 = run b0
  where
  b0 : Chain (Sw12 ∷ K3⁻ ∷ Sw12 ∷ []) (K3⁻ ∷ [])
  b0 = at 0 2 (K3⁻ ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) ((K • iI))) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 X3: 2 steps
lem-sw1-X3 : ⟪ (Sw12 ∷ X3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw1-X3 = run b0
  where
  b0 : Chain (Sw12 ∷ X3 ∷ Sw12 ∷ []) (X3 ∷ [])
  b0 = at 0 2 (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X)) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 Z3: 2 steps
lem-sw1-Z3 : ⟪ (Sw12 ∷ Z3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw1-Z3 = run b0
  where
  b0 : Chain (Sw12 ∷ Z3 ∷ Sw12 ∷ []) (Z3 ∷ [])
  b0 = at 0 2 (Z3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (Z)) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CS01: 3 steps
lem-sw1-CS01 : ⟪ (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw1-CS01 = run b0
  where
  b0 : Chain (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (CS02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CSd01: 3 steps
lem-sw1-CSd01 : ⟪ (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw1-CSd01 = run b0
  where
  b0 : Chain (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (CS02⁻ ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CZ01: 3 steps
lem-sw1-CZ01 : ⟪ (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw1-CZ01 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (CZ02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX01: 3 steps
lem-sw1-CX01 : ⟪ (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw1-CX01 = run b0
  where
  b0 : Chain (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (CX02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK01: 3 steps
lem-sw1-CK01 : ⟪ (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw1-CK01 = run b0
  where
  b0 : Chain (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (CK02 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK02 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd01: 3 steps
lem-sw1-CKd01 : ⟪ (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw1-CKd01 = run b0
  where
  b0 : Chain (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (CK02⁻ ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CS02: 3 steps
lem-sw1-CS02 : ⟪ (Sw12 ∷ CS02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw1-CS02 = run b0
  where
  b0 : Chain (Sw12 ∷ CS02 ∷ Sw12 ∷ []) (CS01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

