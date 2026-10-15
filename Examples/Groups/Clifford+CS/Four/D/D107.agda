{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D107 where

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

-- sw2 CZ23: 2 steps
lem-sw2-CZ23 : ⟪ (Sw23 ∷ CZ23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw2-CZ23 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ23 ∷ Sw23 ∷ []) (CZ23 ∷ [])
  b0 = at 0 2 (CZ23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX23: 2 steps
lem-sw2-CX23 : ⟪ (Sw23 ∷ CX23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw2-CX23 = run b0
  where
  b0 : Chain (Sw23 ∷ CX23 ∷ Sw23 ∷ []) (CX32 ∷ [])
  b0 = at 0 2 (CX32 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CX₀₁ ↑)) ((CX₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK23: 2 steps
lem-sw2-CK23 : ⟪ (Sw23 ∷ CK23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw2-CK23 = run b0
  where
  b0 : Chain (Sw23 ∷ CK23 ∷ Sw23 ∷ []) (CK32 ∷ [])
  b0 = at 0 2 (CK32 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CK₀₁ ↑)) ((CK₁₀ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd23: 2 steps
lem-sw2-CKd23 : ⟪ (Sw23 ∷ CK23⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw2-CKd23 = run b0
  where
  b0 : Chain (Sw23 ∷ CK23⁻ ∷ Sw23 ∷ []) (CK32⁻ ∷ [])
  b0 = at 0 2 (CK32⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • CK₀₁) ↑)) (((S ↑ • CK₁₀) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX30: 3 steps
lem-sw2-CX30 : ⟪ (Sw23 ∷ CX30 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw2-CX30 = run b0
  where
  b0 : Chain (Sw23 ∷ CX30 ∷ Sw23 ∷ []) (CX20 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK30: 3 steps
lem-sw2-CK30 : ⟪ (Sw23 ∷ CK30 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw2-CK30 = run b0
  where
  b0 : Chain (Sw23 ∷ CK30 ∷ Sw23 ∷ []) (CK20 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd30: 3 steps
lem-sw2-CKd30 : ⟪ (Sw23 ∷ CK30⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw2-CKd30 = run b0
  where
  b0 : Chain (Sw23 ∷ CK30⁻ ∷ Sw23 ∷ []) (CK20⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX31: 3 steps
lem-sw2-CX31 : ⟪ (Sw23 ∷ CX31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw2-CX31 = run b0
  where
  b0 : Chain (Sw23 ∷ CX31 ∷ Sw23 ∷ []) (CX21 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK31: 3 steps
lem-sw2-CK31 : ⟪ (Sw23 ∷ CK31 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw2-CK31 = run b0
  where
  b0 : Chain (Sw23 ∷ CK31 ∷ Sw23 ∷ []) (CK21 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd31: 3 steps
lem-sw2-CKd31 : ⟪ (Sw23 ∷ CK31⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw2-CKd31 = run b0
  where
  b0 : Chain (Sw23 ∷ CK31⁻ ∷ Sw23 ∷ []) (CK21⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX32: 2 steps
lem-sw2-CX32 : ⟪ (Sw23 ∷ CX32 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw2-CX32 = run b0
  where
  b0 : Chain (Sw23 ∷ CX32 ∷ Sw23 ∷ []) (CX23 ∷ [])
  b0 = at 0 2 (CX23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CX₁₀ ↑)) ((CX₀₁ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK32: 2 steps
lem-sw2-CK32 : ⟪ (Sw23 ∷ CK32 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw2-CK32 = run b0
  where
  b0 : Chain (Sw23 ∷ CK32 ∷ Sw23 ∷ []) (CK23 ∷ [])
  b0 = at 0 2 (CK23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CK₁₀ ↑)) ((CK₀₁ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd32: 2 steps
lem-sw2-CKd32 : ⟪ (Sw23 ∷ CK32⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw2-CKd32 = run b0
  where
  b0 : Chain (Sw23 ∷ CK32⁻ ∷ Sw23 ∷ []) (CK23⁻ ∷ [])
  b0 = at 0 2 (CK23⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S ↑ • CK₁₀) ↑)) (((S • CK₀₁) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CCZ012: 22 steps
lem-sw2-CCZ012 : ⟪ (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
lem-sw2-CCZ012 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b2 : Chain (Sw23 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (CCZ013 ∷ [])
  b2 = at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CCZ013: 22 steps
lem-sw2-CCZ013 : ⟪ (Sw23 ∷ CCZ013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw2-CCZ013 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw23 ∷ CCZ013 ∷ Sw23 ∷ []) (Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ Sw23 ∷ []) (CCZ012 ∷ [])
  b2 = at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CCZ023: 38 steps
lem-sw2-CCZ023 : ⟪ (Sw23 ∷ CCZ023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-sw2-CCZ023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (Sw23 ∷ CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b1 : Chain (Sw23 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw23 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ Sw23 ∷ [])
  b1 = at 6 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (CS23 ∷ CX03 ∷ CS23⁻ ∷ Sw23 ∷ CX02 ∷ CS03 ∷ Sw23 ∷ []) (Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b3 : Chain (Sw01 ∷ CS23 ∷ Sw23 ∷ Sw01 ∷ CX02 ∷ Sw23 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ []) (Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ [])
  b3 = at 3 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b4 : Chain (Sw01 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ []) (CCZ023 ∷ [])
  b4 = at 4 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

