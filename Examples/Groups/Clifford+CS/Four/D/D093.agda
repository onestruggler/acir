{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D093 where

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

-- sw0 CKd01: 2 steps
lem-sw0-CKd01 : ⟪ (Sw01 ∷ CK01⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw0-CKd01 = run b0
  where
  b0 : Chain (Sw01 ∷ CK01⁻ ∷ Sw01 ∷ []) (CK10⁻ ∷ [])
  b0 = at 0 2 (CK10⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (S • CK₀₁)) ((S ↑ • CK₁₀) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CS02: 2 steps
lem-sw0-CS02 : ⟪ (Sw01 ∷ CS02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw0-CS02 = run b0
  where
  b0 : Chain (Sw01 ∷ CS02 ∷ Sw01 ∷ []) (CS12 ∷ [])
  b0 = at 0 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CSd02: 2 steps
lem-sw0-CSd02 : ⟪ (Sw01 ∷ CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw0-CSd02 = run b0
  where
  b0 : Chain (Sw01 ∷ CS02⁻ ∷ Sw01 ∷ []) (CS12⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CZ02: 2 steps
lem-sw0-CZ02 : ⟪ (Sw01 ∷ CZ02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw0-CZ02 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ02 ∷ Sw01 ∷ []) (CZ12 ∷ [])
  b0 = at 0 2 (CZ12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX02: 2 steps
lem-sw0-CX02 : ⟪ (Sw01 ∷ CX02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw0-CX02 = run b0
  where
  b0 : Chain (Sw01 ∷ CX02 ∷ Sw01 ∷ []) (CX12 ∷ [])
  b0 = at 0 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK02: 2 steps
lem-sw0-CK02 : ⟪ (Sw01 ∷ CK02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw0-CK02 = run b0
  where
  b0 : Chain (Sw01 ∷ CK02 ∷ Sw01 ∷ []) (CK12 ∷ [])
  b0 = at 0 2 (CK12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd02: 2 steps
lem-sw0-CKd02 : ⟪ (Sw01 ∷ CK02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw0-CKd02 = run b0
  where
  b0 : Chain (Sw01 ∷ CK02⁻ ∷ Sw01 ∷ []) (CK12⁻ ∷ [])
  b0 = at 0 2 (CK12⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CS03: 6 steps
lem-sw0-CS03 : ⟪ (Sw01 ∷ CS03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw0-CS03 = run b0
  where
  b0 : Chain (Sw01 ∷ CS03 ∷ Sw01 ∷ []) (CS13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CSd03: 6 steps
lem-sw0-CSd03 : ⟪ (Sw01 ∷ CS03⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw0-CSd03 = run b0
  where
  b0 : Chain (Sw01 ∷ CS03⁻ ∷ Sw01 ∷ []) (CS13⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CS12⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CZ03: 6 steps
lem-sw0-CZ03 : ⟪ (Sw01 ∷ CZ03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw0-CZ03 = run b0
  where
  b0 : Chain (Sw01 ∷ CZ03 ∷ Sw01 ∷ []) (CZ13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CZ12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX03: 6 steps
lem-sw0-CX03 : ⟪ (Sw01 ∷ CX03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw0-CX03 = run b0
  where
  b0 : Chain (Sw01 ∷ CX03 ∷ Sw01 ∷ []) (CX13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK03: 6 steps
lem-sw0-CK03 : ⟪ (Sw01 ∷ CK03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw0-CK03 = run b0
  where
  b0 : Chain (Sw01 ∷ CK03 ∷ Sw01 ∷ []) (CK13 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd03: 6 steps
lem-sw0-CKd03 : ⟪ (Sw01 ∷ CK03⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw0-CKd03 = run b0
  where
  b0 : Chain (Sw01 ∷ CK03⁻ ∷ Sw01 ∷ []) (CK13⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 2 (CK12⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 0 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CX10: 2 steps
lem-sw0-CX10 : ⟪ (Sw01 ∷ CX10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw0-CX10 = run b0
  where
  b0 : Chain (Sw01 ∷ CX10 ∷ Sw01 ∷ []) (CX01 ∷ [])
  b0 = at 0 2 (CX01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CX₁₀) (CX₀₁ • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CK10: 2 steps
lem-sw0-CK10 : ⟪ (Sw01 ∷ CK10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw0-CK10 = run b0
  where
  b0 : Chain (Sw01 ∷ CK10 ∷ Sw01 ∷ []) (CK01 ∷ [])
  b0 = at 0 2 (CK01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • CK₁₀) (CK₀₁ • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- sw0 CKd10: 2 steps
lem-sw0-CKd10 : ⟪ (Sw01 ∷ CK10⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw0-CKd10 = run b0
  where
  b0 : Chain (Sw01 ∷ CK10⁻ ∷ Sw01 ∷ []) (CK01⁻ ∷ [])
  b0 = at 0 2 (CK01⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (S ↑ • CK₁₀)) ((S • CK₀₁) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

