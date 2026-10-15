{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D104 where

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

-- sw2 Z2: 2 steps
lem-sw2-Z2 : ⟪ (Sw23 ∷ Z2 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw2-Z2 = run b0
  where
  b0 : Chain (Sw23 ∷ Z2 ∷ Sw23 ∷ []) (Z3 ∷ [])
  b0 = at 0 2 (Z3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 S3: 2 steps
lem-sw2-S3 : ⟪ (Sw23 ∷ S3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw2-S3 = run b0
  where
  b0 : Chain (Sw23 ∷ S3 ∷ Sw23 ∷ []) (S2 ∷ [])
  b0 = at 0 2 (S2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑ ↑)) ((S ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Sd3: 2 steps
lem-sw2-Sd3 : ⟪ (Sw23 ∷ S3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw2-Sd3 = run b0
  where
  b0 : Chain (Sw23 ∷ S3⁻ ∷ Sw23 ∷ []) (S2⁻ ∷ [])
  b0 = at 0 2 (S2⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 K3: 2 steps
lem-sw2-K3 : ⟪ (Sw23 ∷ K3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw2-K3 = run b0
  where
  b0 : Chain (Sw23 ∷ K3 ∷ Sw23 ∷ []) (K2 ∷ [])
  b0 = at 0 2 (K2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (K ↑ ↑)) ((K ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Kd3: 2 steps
lem-sw2-Kd3 : ⟪ (Sw23 ∷ K3⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw2-Kd3 = run b0
  where
  b0 : Chain (Sw23 ∷ K3⁻ ∷ Sw23 ∷ []) (K2⁻ ∷ [])
  b0 = at 0 2 (K2⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((K • iI) ↑ ↑)) (((K • iI) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 X3: 2 steps
lem-sw2-X3 : ⟪ (Sw23 ∷ X3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw2-X3 = run b0
  where
  b0 : Chain (Sw23 ∷ X3 ∷ Sw23 ∷ []) (X2 ∷ [])
  b0 = at 0 2 (X2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑ ↑)) ((X ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 Z3: 2 steps
lem-sw2-Z3 : ⟪ (Sw23 ∷ Z3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw2-Z3 = run b0
  where
  b0 : Chain (Sw23 ∷ Z3 ∷ Sw23 ∷ []) (Z2 ∷ [])
  b0 = at 0 2 (Z2 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Z ↑ ↑)) ((Z ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CS01: 2 steps
lem-sw2-CS01 : ⟪ (Sw23 ∷ CS01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw2-CS01 = run b0
  where
  b0 : Chain (Sw23 ∷ CS01 ∷ Sw23 ∷ []) (CS01 ∷ [])
  b0 = at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CSd01: 2 steps
lem-sw2-CSd01 : ⟪ (Sw23 ∷ CS01⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw2-CSd01 = run b0
  where
  b0 : Chain (Sw23 ∷ CS01⁻ ∷ Sw23 ∷ []) (CS01⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CZ01: 2 steps
lem-sw2-CZ01 : ⟪ (Sw23 ∷ CZ01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw2-CZ01 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ01 ∷ Sw23 ∷ []) (CZ01 ∷ [])
  b0 = at 0 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX01: 2 steps
lem-sw2-CX01 : ⟪ (Sw23 ∷ CX01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw2-CX01 = run b0
  where
  b0 : Chain (Sw23 ∷ CX01 ∷ Sw23 ∷ []) (CX01 ∷ [])
  b0 = at 0 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK01: 2 steps
lem-sw2-CK01 : ⟪ (Sw23 ∷ CK01 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw2-CK01 = run b0
  where
  b0 : Chain (Sw23 ∷ CK01 ∷ Sw23 ∷ []) (CK01 ∷ [])
  b0 = at 0 2 (CK01 ∷ Sw23 ∷ []) (sym (low-comm (CK₀₁) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd01: 2 steps
lem-sw2-CKd01 : ⟪ (Sw23 ∷ CK01⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw2-CKd01 = run b0
  where
  b0 : Chain (Sw23 ∷ CK01⁻ ∷ Sw23 ∷ []) (CK01⁻ ∷ [])
  b0 = at 0 2 (CK01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S • CK₀₁)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CS02: 3 steps
lem-sw2-CS02 : ⟪ (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw2-CS02 = run b0
  where
  b0 : Chain (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CS03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CSd02: 3 steps
lem-sw2-CSd02 : ⟪ (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw2-CSd02 = run b0
  where
  b0 : Chain (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (CS03⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CZ02: 3 steps
lem-sw2-CZ02 : ⟪ (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw2-CZ02 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (CZ03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

