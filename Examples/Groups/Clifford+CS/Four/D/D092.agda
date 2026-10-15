{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D092 where

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

-- sw0 Sd2: 2 steps
lem-sw0-Sd2 : ⟪ (Sw01 ∷ S2⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw0-Sd2 = run b0
  where
  b0 : Chain (Sw01 ∷ S2⁻ ∷ Sw01 ∷ []) (S2⁻ ∷ [])
  b0 = at 0 2 (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 K2: 2 steps
lem-sw0-K2 : ⟪ (Sw01 ∷ K2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw0-K2 = run b0
  where
  b0 : Chain (Sw01 ∷ K2 ∷ Sw01 ∷ []) (K2 ∷ [])
  b0 = at 0 2 (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 Kd2: 2 steps
lem-sw0-Kd2 : ⟪ (Sw01 ∷ K2⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw0-Kd2 = run b0
  where
  b0 : Chain (Sw01 ∷ K2⁻ ∷ Sw01 ∷ []) (K2⁻ ∷ [])
  b0 = at 0 2 (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 X2: 2 steps
lem-sw0-X2 : ⟪ (Sw01 ∷ X2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw0-X2 = run b0
  where
  b0 : Chain (Sw01 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ [])
  b0 = at 0 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 Z2: 2 steps
lem-sw0-Z2 : ⟪ (Sw01 ∷ Z2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw0-Z2 = run b0
  where
  b0 : Chain (Sw01 ∷ Z2 ∷ Sw01 ∷ []) (Z2 ∷ [])
  b0 = at 0 2 (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z)) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 S3: 2 steps
lem-sw0-S3 : ⟪ (Sw01 ∷ S3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw0-S3 = run b0
  where
  b0 : Chain (Sw01 ∷ S3 ∷ Sw01 ∷ []) (S3 ∷ [])
  b0 = at 0 2 (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 Sd3: 2 steps
lem-sw0-Sd3 : ⟪ (Sw01 ∷ S3⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw0-Sd3 = run b0
  where
  b0 : Chain (Sw01 ∷ S3⁻ ∷ Sw01 ∷ []) (S3⁻ ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 K3: 2 steps
lem-sw0-K3 : ⟪ (Sw01 ∷ K3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw0-K3 = run b0
  where
  b0 : Chain (Sw01 ∷ K3 ∷ Sw01 ∷ []) (K3 ∷ [])
  b0 = at 0 2 (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 Kd3: 2 steps
lem-sw0-Kd3 : ⟪ (Sw01 ∷ K3⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw0-Kd3 = run b0
  where
  b0 : Chain (Sw01 ∷ K3⁻ ∷ Sw01 ∷ []) (K3⁻ ∷ [])
  b0 = at 0 2 (K3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((K • iI) ↑))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 X3: 2 steps
lem-sw0-X3 : ⟪ (Sw01 ∷ X3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw0-X3 = run b0
  where
  b0 : Chain (Sw01 ∷ X3 ∷ Sw01 ∷ []) (X3 ∷ [])
  b0 = at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 Z3: 2 steps
lem-sw0-Z3 : ⟪ (Sw01 ∷ Z3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw0-Z3 = run b0
  where
  b0 : Chain (Sw01 ∷ Z3 ∷ Sw01 ∷ []) (Z3 ∷ [])
  b0 = at 0 2 (Z3 ∷ Sw01 ∷ []) (low-comm (Swap) ((Z ↑))) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CS01: 2 steps
lem-sw0-CS01 : ⟪ (Sw01 ∷ CS01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw0-CS01 = run b0
  where
  b0 : Chain (Sw01 ∷ CS01 ∷ Sw01 ∷ []) (CS01 ∷ [])
  b0 = at 0 2 (CS01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CS) (CS • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CSd01: 2 steps
lem-sw0-CSd01 : ⟪ (Sw01 ∷ CS01⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw0-CSd01 = run b0
  where
  b0 : Chain (Sw01 ∷ CS01⁻ ∷ Sw01 ∷ []) (CS01⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS • CS • CS)) ((CS • CS • CS) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CZ01: 2 steps
lem-sw0-CZ01 : ⟪ (Sw01 ∷ CZ01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw0-CZ01 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ01 ∷ Sw01 ∷ []) (CZ01 ∷ [])
  b0 = at 0 2 (CZ01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CZ) (CZ • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX01: 2 steps
lem-sw0-CX01 : ⟪ (Sw01 ∷ CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw0-CX01 = run b0
  where
  b0 : Chain (Sw01 ∷ CX01 ∷ Sw01 ∷ []) (CX10 ∷ [])
  b0 = at 0 2 (CX10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₀₁) (CX₁₀ • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK01: 2 steps
lem-sw0-CK01 : ⟪ (Sw01 ∷ CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw0-CK01 = run b0
  where
  b0 : Chain (Sw01 ∷ CK01 ∷ Sw01 ∷ []) (CK10 ∷ [])
  b0 = at 0 2 (CK10 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CK₀₁) (CK₁₀ • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

