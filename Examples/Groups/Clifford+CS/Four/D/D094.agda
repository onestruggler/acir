{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D094 where

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

-- sw0 CS12: 2 steps
lem-sw0-CS12 : ⟪ (Sw01 ∷ CS12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw0-CS12 = run b0
  where
  b0 : Chain (Sw01 ∷ CS12 ∷ Sw01 ∷ []) (CS02 ∷ [])
  b0 = at 0 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CSd12: 2 steps
lem-sw0-CSd12 : ⟪ (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw0-CSd12 = run b0
  where
  b0 : Chain (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) (CS02⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CZ12: 2 steps
lem-sw0-CZ12 : ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw0-CZ12 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) (CZ02 ∷ [])
  b0 = at 0 2 (CZ02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX12: 2 steps
lem-sw0-CX12 : ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw0-CX12 = run b0
  where
  b0 : Chain (Sw01 ∷ CX12 ∷ Sw01 ∷ []) (CX02 ∷ [])
  b0 = at 0 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK12: 2 steps
lem-sw0-CK12 : ⟪ (Sw01 ∷ CK12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw0-CK12 = run b0
  where
  b0 : Chain (Sw01 ∷ CK12 ∷ Sw01 ∷ []) (CK02 ∷ [])
  b0 = at 0 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd12: 2 steps
lem-sw0-CKd12 : ⟪ (Sw01 ∷ CK12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw0-CKd12 = run b0
  where
  b0 : Chain (Sw01 ∷ CK12⁻ ∷ Sw01 ∷ []) (CK02⁻ ∷ [])
  b0 = at 0 2 (CK02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CS13: 6 steps
lem-sw0-CS13 : ⟪ (Sw01 ∷ CS13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw0-CS13 = run b0
  where
  b0 : Chain (Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CSd13: 6 steps
lem-sw0-CSd13 : ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw0-CSd13 = run b0
  where
  b0 : Chain (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) (CS03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CZ13: 6 steps
lem-sw0-CZ13 : ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw0-CZ13 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) (CZ03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CZ02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX13: 6 steps
lem-sw0-CX13 : ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw0-CX13 = run b0
  where
  b0 : Chain (Sw01 ∷ CX13 ∷ Sw01 ∷ []) (CX03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK13: 6 steps
lem-sw0-CK13 : ⟪ (Sw01 ∷ CK13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw0-CK13 = run b0
  where
  b0 : Chain (Sw01 ∷ CK13 ∷ Sw01 ∷ []) (CK03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd13: 6 steps
lem-sw0-CKd13 : ⟪ (Sw01 ∷ CK13⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw0-CKd13 = run b0
  where
  b0 : Chain (Sw01 ∷ CK13⁻ ∷ Sw01 ∷ []) (CK03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX20: 2 steps
lem-sw0-CX20 : ⟪ (Sw01 ∷ CX20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw0-CX20 = run b0
  where
  b0 : Chain (Sw01 ∷ CX20 ∷ Sw01 ∷ []) (CX21 ∷ [])
  b0 = at 0 2 (CX21 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK20: 2 steps
lem-sw0-CK20 : ⟪ (Sw01 ∷ CK20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw0-CK20 = run b0
  where
  b0 : Chain (Sw01 ∷ CK20 ∷ Sw01 ∷ []) (CK21 ∷ [])
  b0 = at 0 2 (CK21 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd20: 2 steps
lem-sw0-CKd20 : ⟪ (Sw01 ∷ CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw0-CKd20 = run b0
  where
  b0 : Chain (Sw01 ∷ CK20⁻ ∷ Sw01 ∷ []) (CK21⁻ ∷ [])
  b0 = at 0 2 (CK21⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX21: 2 steps
lem-sw0-CX21 : ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw0-CX21 = run b0
  where
  b0 : Chain (Sw01 ∷ CX21 ∷ Sw01 ∷ []) (CX20 ∷ [])
  b0 = at 0 2 (CX20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

