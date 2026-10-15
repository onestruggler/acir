{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D101 where

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

-- sw1 CS23: 2 steps
lem-sw1-CS23 : ⟪ (Sw12 ∷ CS23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw1-CS23 = run b0
  where
  b0 : Chain (Sw12 ∷ CS23 ∷ Sw12 ∷ []) (CS13 ∷ [])
  b0 = at 0 2 (CS13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CSd23: 2 steps
lem-sw1-CSd23 : ⟪ (Sw12 ∷ CS23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw1-CSd23 = run b0
  where
  b0 : Chain (Sw12 ∷ CS23⁻ ∷ Sw12 ∷ []) (CS13⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CZ23: 2 steps
lem-sw1-CZ23 : ⟪ (Sw12 ∷ CZ23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw1-CZ23 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ23 ∷ Sw12 ∷ []) (CZ13 ∷ [])
  b0 = at 0 2 (CZ13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CZ ↑)) ((Swap ↑ • CZ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX23: 2 steps
lem-sw1-CX23 : ⟪ (Sw12 ∷ CX23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw1-CX23 = run b0
  where
  b0 : Chain (Sw12 ∷ CX23 ∷ Sw12 ∷ []) (CX13 ∷ [])
  b0 = at 0 2 (CX13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK23: 2 steps
lem-sw1-CK23 : ⟪ (Sw12 ∷ CK23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw1-CK23 = run b0
  where
  b0 : Chain (Sw12 ∷ CK23 ∷ Sw12 ∷ []) (CK13 ∷ [])
  b0 = at 0 2 (CK13 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CK₀₁ ↑)) ((Swap ↑ • CK₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd23: 2 steps
lem-sw1-CKd23 : ⟪ (Sw12 ∷ CK23⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw1-CKd23 = run b0
  where
  b0 : Chain (Sw12 ∷ CK23⁻ ∷ Sw12 ∷ []) (CK13⁻ ∷ [])
  b0 = at 0 2 (CK13⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((S • CK₀₁) ↑)) ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX30: 6 steps
lem-sw1-CX30 : ⟪ (Sw12 ∷ CX30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw1-CX30 = run b0
  where
  b0 : Chain (Sw12 ∷ CX30 ∷ Sw12 ∷ []) (CX30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK30: 6 steps
lem-sw1-CK30 : ⟪ (Sw12 ∷ CK30 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw1-CK30 = run b0
  where
  b0 : Chain (Sw12 ∷ CK30 ∷ Sw12 ∷ []) (CK30 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd30: 6 steps
lem-sw1-CKd30 : ⟪ (Sw12 ∷ CK30⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw1-CKd30 = run b0
  where
  b0 : Chain (Sw12 ∷ CK30⁻ ∷ Sw12 ∷ []) (CK30⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX31: 2 steps
lem-sw1-CX31 : ⟪ (Sw12 ∷ CX31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw1-CX31 = run b0
  where
  b0 : Chain (Sw12 ∷ CX31 ∷ Sw12 ∷ []) (CX32 ∷ [])
  b0 = at 0 2 (CX32 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CX₁₀ • Swap ↑)) ((CX₁₀ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK31: 2 steps
lem-sw1-CK31 : ⟪ (Sw12 ∷ CK31 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw1-CK31 = run b0
  where
  b0 : Chain (Sw12 ∷ CK31 ∷ Sw12 ∷ []) (CK32 ∷ [])
  b0 = at 0 2 (CK32 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • CK₁₀ • Swap ↑)) ((CK₁₀ ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd31: 2 steps
lem-sw1-CKd31 : ⟪ (Sw12 ∷ CK31⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw1-CKd31 = run b0
  where
  b0 : Chain (Sw12 ∷ CK31⁻ ∷ Sw12 ∷ []) (CK32⁻ ∷ [])
  b0 = at 0 2 (CK32⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (((S ↑ • CK₁₀) ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX32: 2 steps
lem-sw1-CX32 : ⟪ (Sw12 ∷ CX32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw1-CX32 = run b0
  where
  b0 : Chain (Sw12 ∷ CX32 ∷ Sw12 ∷ []) (CX31 ∷ [])
  b0 = at 0 2 (CX31 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CX₁₀ ↑)) ((Swap ↑ • CX₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK32: 2 steps
lem-sw1-CK32 : ⟪ (Sw12 ∷ CK32 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw1-CK32 = run b0
  where
  b0 : Chain (Sw12 ∷ CK32 ∷ Sw12 ∷ []) (CK31 ∷ [])
  b0 = at 0 2 (CK31 ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd32: 2 steps
lem-sw1-CKd32 : ⟪ (Sw12 ∷ CK32⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw1-CKd32 = run b0
  where
  b0 : Chain (Sw12 ∷ CK32⁻ ∷ Sw12 ∷ []) (CK31⁻ ∷ [])
  b0 = at 0 2 (CK31⁻ ∷ Sw12 ∷ []) (win 0 3 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CCZ012: 12 steps
lem-sw1-CCZ012 : ⟪ (Sw12 ∷ CCZ012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw1-CCZ012 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ CCZ012 ∷ Sw12 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ Sw12 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw12 ∷ []) (CCZ012 ∷ [])
  b1 = at 4 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • ((CS • CS • CS) ↑) • (Swap ↑ • CX₀₁ • Swap ↑) • CS) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

