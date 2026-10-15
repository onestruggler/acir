{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D106 where

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

-- sw2 CK12: 3 steps
lem-sw2-CK12 : ⟪ (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw2-CK12 = run b0
  where
  b0 : Chain (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (CK13 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd12: 3 steps
lem-sw2-CKd12 : ⟪ (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw2-CKd12 = run b0
  where
  b0 : Chain (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (CK13⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CS13: 3 steps
lem-sw2-CS13 : ⟪ (Sw23 ∷ CS13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw2-CS13 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13 ∷ Sw23 ∷ []) (CS12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CSd13: 3 steps
lem-sw2-CSd13 : ⟪ (Sw23 ∷ CS13⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw2-CSd13 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13⁻ ∷ Sw23 ∷ []) (CS12⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CZ13: 3 steps
lem-sw2-CZ13 : ⟪ (Sw23 ∷ CZ13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw2-CZ13 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ13 ∷ Sw23 ∷ []) (CZ12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX13: 3 steps
lem-sw2-CX13 : ⟪ (Sw23 ∷ CX13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw2-CX13 = run b0
  where
  b0 : Chain (Sw23 ∷ CX13 ∷ Sw23 ∷ []) (CX12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK13: 3 steps
lem-sw2-CK13 : ⟪ (Sw23 ∷ CK13 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw2-CK13 = run b0
  where
  b0 : Chain (Sw23 ∷ CK13 ∷ Sw23 ∷ []) (CK12 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd13: 3 steps
lem-sw2-CKd13 : ⟪ (Sw23 ∷ CK13⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw2-CKd13 = run b0
  where
  b0 : Chain (Sw23 ∷ CK13⁻ ∷ Sw23 ∷ []) (CK12⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX20: 3 steps
lem-sw2-CX20 : ⟪ (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw2-CX20 = run b0
  where
  b0 : Chain (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (CX30 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK20: 3 steps
lem-sw2-CK20 : ⟪ (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw2-CK20 = run b0
  where
  b0 : Chain (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (CK30 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd20: 3 steps
lem-sw2-CKd20 : ⟪ (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw2-CKd20 = run b0
  where
  b0 : Chain (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (CK30⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CX21: 3 steps
lem-sw2-CX21 : ⟪ (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw2-CX21 = run b0
  where
  b0 : Chain (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (CX31 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CK21: 3 steps
lem-sw2-CK21 : ⟪ (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw2-CK21 = run b0
  where
  b0 : Chain (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (CK31 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CKd21: 3 steps
lem-sw2-CKd21 : ⟪ (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw2-CKd21 = run b0
  where
  b0 : Chain (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (CK31⁻ ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CS23: 2 steps
lem-sw2-CS23 : ⟪ (Sw23 ∷ CS23 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw2-CS23 = run b0
  where
  b0 : Chain (Sw23 ∷ CS23 ∷ Sw23 ∷ []) (CS23 ∷ [])
  b0 = at 0 2 (CS23 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw2 CSd23: 2 steps
lem-sw2-CSd23 : ⟪ (Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw2-CSd23 = run b0
  where
  b0 : Chain (Sw23 ∷ CS23⁻ ∷ Sw23 ∷ []) (CS23⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

