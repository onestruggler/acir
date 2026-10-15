{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D099 where

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

-- sw1 CSd02: 3 steps
lem-sw1-CSd02 : ⟪ (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw1-CSd02 = run b0
  where
  b0 : Chain (Sw12 ∷ CS02⁻ ∷ Sw12 ∷ []) (CS01⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CZ02: 3 steps
lem-sw1-CZ02 : ⟪ (Sw12 ∷ CZ02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw1-CZ02 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ02 ∷ Sw12 ∷ []) (CZ01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX02: 3 steps
lem-sw1-CX02 : ⟪ (Sw12 ∷ CX02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw1-CX02 = run b0
  where
  b0 : Chain (Sw12 ∷ CX02 ∷ Sw12 ∷ []) (CX01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK02: 3 steps
lem-sw1-CK02 : ⟪ (Sw12 ∷ CK02 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw1-CK02 = run b0
  where
  b0 : Chain (Sw12 ∷ CK02 ∷ Sw12 ∷ []) (CK01 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd02: 3 steps
lem-sw1-CKd02 : ⟪ (Sw12 ∷ CK02⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw1-CKd02 = run b0
  where
  b0 : Chain (Sw12 ∷ CK02⁻ ∷ Sw12 ∷ []) (CK01⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CS03: 6 steps
lem-sw1-CS03 : ⟪ (Sw12 ∷ CS03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw1-CS03 = run b0
  where
  b0 : Chain (Sw12 ∷ CS03 ∷ Sw12 ∷ []) (CS03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CSd03: 6 steps
lem-sw1-CSd03 : ⟪ (Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw1-CSd03 = run b0
  where
  b0 : Chain (Sw12 ∷ CS03⁻ ∷ Sw12 ∷ []) (CS03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CZ03: 6 steps
lem-sw1-CZ03 : ⟪ (Sw12 ∷ CZ03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw1-CZ03 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ03 ∷ Sw12 ∷ []) (CZ03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CZ01 ∷ Sw23 ∷ []) (sym (low-comm (CZ) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX03: 6 steps
lem-sw1-CX03 : ⟪ (Sw12 ∷ CX03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw1-CX03 = run b0
  where
  b0 : Chain (Sw12 ∷ CX03 ∷ Sw12 ∷ []) (CX03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK03: 6 steps
lem-sw1-CK03 : ⟪ (Sw12 ∷ CK03 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw1-CK03 = run b0
  where
  b0 : Chain (Sw12 ∷ CK03 ∷ Sw12 ∷ []) (CK03 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CK01 ∷ Sw23 ∷ []) (sym (low-comm (CK₀₁) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd03: 6 steps
lem-sw1-CKd03 : ⟪ (Sw12 ∷ CK03⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw1-CKd03 = run b0
  where
  b0 : Chain (Sw12 ∷ CK03⁻ ∷ Sw12 ∷ []) (CK03⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (win 0 3 complete₃ (Swap • (Swap ↑) • Swap) ((Swap ↑) • Swap • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (CK01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S • CK₀₁)) (Swap))) ▸
       at 3 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (win 0 3 complete₃ ((Swap ↑) • Swap • (Swap ↑)) (Swap • (Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 0 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CX10: 3 steps
lem-sw1-CX10 : ⟪ (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw1-CX10 = run b0
  where
  b0 : Chain (Sw12 ∷ CX10 ∷ Sw12 ∷ []) (CX20 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CK10: 3 steps
lem-sw1-CK10 : ⟪ (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw1-CK10 = run b0
  where
  b0 : Chain (Sw12 ∷ CK10 ∷ Sw12 ∷ []) (CK20 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK20 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CKd10: 3 steps
lem-sw1-CKd10 : ⟪ (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw1-CKd10 = run b0
  where
  b0 : Chain (Sw12 ∷ CK10⁻ ∷ Sw12 ∷ []) (CK20⁻ ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (win 3 0 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CK20⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CS12: 2 steps
lem-sw1-CS12 : ⟪ (Sw12 ∷ CS12 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw1-CS12 = run b0
  where
  b0 : Chain (Sw12 ∷ CS12 ∷ Sw12 ∷ []) (CS12 ∷ [])
  b0 = at 0 2 (CS12 ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • (CS ↑)) ((CS ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- sw1 CSd12: 2 steps
lem-sw1-CSd12 : ⟪ (Sw12 ∷ CS12⁻ ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw1-CSd12 = run b0
  where
  b0 : Chain (Sw12 ∷ CS12⁻ ∷ Sw12 ∷ []) (CS12⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ Sw12 ∷ []) (win 3 0 complete₃ ((Swap ↑) • ((CS • CS • CS) ↑)) (((CS • CS • CS) ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 [] (win 3 0 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

