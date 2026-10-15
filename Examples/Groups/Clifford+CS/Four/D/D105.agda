{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D105 where

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

-- sw2 CX02: 3 steps
lem-sw2-CX02 : ⟪ (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw2-CX02 = run b0
  where
  b0 : Chain (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (CX03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK02: 3 steps
lem-sw2-CK02 : ⟪ (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw2-CK02 = run b0
  where
  b0 : Chain (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (CK03 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd02: 3 steps
lem-sw2-CKd02 : ⟪ (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw2-CKd02 = run b0
  where
  b0 : Chain (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (CK03⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CS03: 3 steps
lem-sw2-CS03 : ⟪ (Sw23 ∷ CS03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw2-CS03 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03 ∷ Sw23 ∷ []) (CS02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CSd03: 3 steps
lem-sw2-CSd03 : ⟪ (Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw2-CSd03 = run b0
  where
  b0 : Chain (Sw23 ∷ CS03⁻ ∷ Sw23 ∷ []) (CS02⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CZ03: 3 steps
lem-sw2-CZ03 : ⟪ (Sw23 ∷ CZ03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw2-CZ03 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ03 ∷ Sw23 ∷ []) (CZ02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX03: 3 steps
lem-sw2-CX03 : ⟪ (Sw23 ∷ CX03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw2-CX03 = run b0
  where
  b0 : Chain (Sw23 ∷ CX03 ∷ Sw23 ∷ []) (CX02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK03: 3 steps
lem-sw2-CK03 : ⟪ (Sw23 ∷ CK03 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw2-CK03 = run b0
  where
  b0 : Chain (Sw23 ∷ CK03 ∷ Sw23 ∷ []) (CK02 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd03: 3 steps
lem-sw2-CKd03 : ⟪ (Sw23 ∷ CK03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw2-CKd03 = run b0
  where
  b0 : Chain (Sw23 ∷ CK03⁻ ∷ Sw23 ∷ []) (CK02⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX10: 2 steps
lem-sw2-CX10 : ⟪ (Sw23 ∷ CX10 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw2-CX10 = run b0
  where
  b0 : Chain (Sw23 ∷ CX10 ∷ Sw23 ∷ []) (CX10 ∷ [])
  b0 = at 0 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK10: 2 steps
lem-sw2-CK10 : ⟪ (Sw23 ∷ CK10 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw2-CK10 = run b0
  where
  b0 : Chain (Sw23 ∷ CK10 ∷ Sw23 ∷ []) (CK10 ∷ [])
  b0 = at 0 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd10: 2 steps
lem-sw2-CKd10 : ⟪ (Sw23 ∷ CK10⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw2-CKd10 = run b0
  where
  b0 : Chain (Sw23 ∷ CK10⁻ ∷ Sw23 ∷ []) (CK10⁻ ∷ [])
  b0 = at 0 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CS12: 3 steps
lem-sw2-CS12 : ⟪ (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw2-CS12 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (CS13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CSd12: 3 steps
lem-sw2-CSd12 : ⟪ (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw2-CSd12 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (CS13⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CZ12: 3 steps
lem-sw2-CZ12 : ⟪ (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw2-CZ12 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (CZ13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX12: 3 steps
lem-sw2-CX12 : ⟪ (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw2-CX12 = run b0
  where
  b0 : Chain (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (CX13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

