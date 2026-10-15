{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D100 where

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

-- sw1 CZ12: 2 steps
lem-sw1-CZ12 : ⟪ (Sw12 ∷ CZ12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw1-CZ12 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ12 ∷ Sw12 ∷ []) (CZ12 ∷ [])
  b0 = at 0 2 (CZ12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX12: 2 steps
lem-sw1-CX12 : ⟪ (Sw12 ∷ CX12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw1-CX12 = run b0
  where
  b0 : Chain (Sw12 ∷ CX12 ∷ Sw12 ∷ []) (CX21 ∷ [])
  b0 = at 0 2 (CX21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK12: 2 steps
lem-sw1-CK12 : ⟪ (Sw12 ∷ CK12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw1-CK12 = run b0
  where
  b0 : Chain (Sw12 ∷ CK12 ∷ Sw12 ∷ []) (CK21 ∷ [])
  b0 = at 0 2 (CK21 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd12: 2 steps
lem-sw1-CKd12 : ⟪ (Sw12 ∷ CK12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw1-CKd12 = run b0
  where
  b0 : Chain (Sw12 ∷ CK12⁻ ∷ Sw12 ∷ []) (CK21⁻ ∷ [])
  b0 = at 0 2 (CK21⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CS13: 2 steps
lem-sw1-CS13 : ⟪ (Sw12 ∷ CS13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw1-CS13 = run b0
  where
  b0 : Chain (Sw12 ∷ CS13 ∷ Sw12 ∷ []) (CS23 ∷ [])
  b0 = at 0 2 (CS23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CSd13: 2 steps
lem-sw1-CSd13 : ⟪ (Sw12 ∷ CS13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw1-CSd13 = run b0
  where
  b0 : Chain (Sw12 ∷ CS13⁻ ∷ Sw12 ∷ []) (CS23⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((CS • CS • CS) ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CZ13: 2 steps
lem-sw1-CZ13 : ⟪ (Sw12 ∷ CZ13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw1-CZ13 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ13 ∷ Sw12 ∷ []) (CZ23 ∷ [])
  b0 = at 0 2 (CZ23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX13: 2 steps
lem-sw1-CX13 : ⟪ (Sw12 ∷ CX13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw1-CX13 = run b0
  where
  b0 : Chain (Sw12 ∷ CX13 ∷ Sw12 ∷ []) (CX23 ∷ [])
  b0 = at 0 2 (CX23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK13: 2 steps
lem-sw1-CK13 : ⟪ (Sw12 ∷ CK13 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw1-CK13 = run b0
  where
  b0 : Chain (Sw12 ∷ CK13 ∷ Sw12 ∷ []) (CK23 ∷ [])
  b0 = at 0 2 (CK23 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CK₀₁ • Swap ↑)) ((CK₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd13: 2 steps
lem-sw1-CKd13 : ⟪ (Sw12 ∷ CK13⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw1-CKd13 = run b0
  where
  b0 : Chain (Sw12 ∷ CK13⁻ ∷ Sw12 ∷ []) (CK23⁻ ∷ [])
  b0 = at 0 2 (CK23⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (((S • CK₀₁) ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX20: 3 steps
lem-sw1-CX20 : ⟪ (Sw12 ∷ CX20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw1-CX20 = run b0
  where
  b0 : Chain (Sw12 ∷ CX20 ∷ Sw12 ∷ []) (CX10 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK20: 3 steps
lem-sw1-CK20 : ⟪ (Sw12 ∷ CK20 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw1-CK20 = run b0
  where
  b0 : Chain (Sw12 ∷ CK20 ∷ Sw12 ∷ []) (CK10 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd20: 3 steps
lem-sw1-CKd20 : ⟪ (Sw12 ∷ CK20⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw1-CKd20 = run b0
  where
  b0 : Chain (Sw12 ∷ CK20⁻ ∷ Sw12 ∷ []) (CK10⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX21: 2 steps
lem-sw1-CX21 : ⟪ (Sw12 ∷ CX21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw1-CX21 = run b0
  where
  b0 : Chain (Sw12 ∷ CX21 ∷ Sw12 ∷ []) (CX12 ∷ [])
  b0 = at 0 2 (CX12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK21: 2 steps
lem-sw1-CK21 : ⟪ (Sw12 ∷ CK21 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw1-CK21 = run b0
  where
  b0 : Chain (Sw12 ∷ CK21 ∷ Sw12 ∷ []) (CK12 ∷ [])
  b0 = at 0 2 (CK12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd21: 2 steps
lem-sw1-CKd21 : ⟪ (Sw12 ∷ CK21⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw1-CKd21 = run b0
  where
  b0 : Chain (Sw12 ∷ CK21⁻ ∷ Sw12 ∷ []) (CK12⁻ ∷ [])
  b0 = at 0 2 (CK12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

