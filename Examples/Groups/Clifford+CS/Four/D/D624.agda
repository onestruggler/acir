{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D624 where

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
open import Examples.Groups.Clifford+CS.Four.D.D038 using (lem-pass-CZ12-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D049 using (lem-pass-CCZ123-vs-CS03)
-- pass [CCZ123] [X1 CS01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CS01-X1 : ⟪ (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CS01-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CS01 ∷ CX23 ∷ []) (sym (low-comm (CS) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 4 (X1 ∷ CS01 ∷ X1 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑) • CS • (X ↑)) ((X ↑) • CS • (X ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CS01 ∷ CX23 ∷ []) (sym (low-comm (CS) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 4 (X1 ∷ CS01 ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • CS • (X ↑)) ((X ↑) • CS • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CS01 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 4 (X1 ∷ CS01 ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • CS • (X ↑)) ((X ↑) • CS • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X1 CK10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CK10-X1 : ⟪ (CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CK10-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CK10 ∷ CX23 ∷ []) (sym (low-comm (CK₁₀) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 4 (X1 ∷ CK10 ∷ X1 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑) • CK₁₀ • (X ↑)) ((X ↑) • CK₁₀ • (X ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CK10 ∷ CX23 ∷ []) (sym (low-comm (CK₁₀) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10 ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 4 (X1 ∷ CK10 ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • CK₁₀ • (X ↑)) ((X ↑) • CK₁₀ • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CK10 ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 4 (X1 ∷ CK10 ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • CK₁₀ • (X ↑)) ((X ↑) • CK₁₀ • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CS03] [iI]: 9 steps
lem-pass-CS03-vs-iI : ⟪ (CS03 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-iI = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ ι ∷ []) (ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • iI) (iI • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (ι ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (ι ∷ CS03 ∷ [])
  b1 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [Z1]: 9 steps
lem-pass-CS03-vs-Z1 : ⟪ (CS03 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z1 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Z1 ∷ []) (Z1 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Z1 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Z ↑)) ((Z ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (Z1 ∷ Sw23 ∷ []) (sym (low-comm ((Z ↑)) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z1 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (Z1 ∷ CS03 ∷ [])
  b1 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [Z2]: 15 steps
lem-pass-CS03-vs-Z2 : ⟪ (CS03 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Z2 ∷ []) (Sw01 ∷ Z2 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Z2 ∷ []) (sym (low-comm (Swap) (Z))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Z2 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Z ↑)) ((Z ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ Z2 ∷ CS13 ∷ Sw01 ∷ []) (Z2 ∷ CS03 ∷ [])
  b1 = at 0 2 (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z)) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [CZ12]: 1 steps
lem-pass-CS03-vs-CZ12 : ⟪ (CS03 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ12 = run b0
  where
  b0 : Chain (CS03 ∷ CZ12 ∷ []) (CZ12 ∷ CS03 ∷ [])
  b0 = at 0 2 (CZ12 ∷ CS03 ∷ []) (sym lem-pass-CZ12-vs-CS03) ▸ done


-- pass [CS03] [Z3]: 9 steps
lem-pass-CS03-vs-Z3 : ⟪ (CS03 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Z3 ∷ []) (Z3 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ Z2 ∷ []) (win 0 3 complete₃ ((Z ↑ ↑) • (Swap ↑)) ((Swap ↑) • (Z ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Z2 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Z ↑ ↑)) ((Z ↑ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (Z3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (Z ↑)) ((Z ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Z3 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ []) (Z3 ∷ CS03 ∷ [])
  b1 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [CZ13]: 11 steps
lem-pass-CS03-vs-CZ13 : ⟪ (CS03 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ13 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CZ13 ∷ []) (CZ13 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CZ12 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ13 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ []) (CZ13 ∷ CS03 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [CZ23]: 15 steps
lem-pass-CS03-vs-CZ23 : ⟪ (CS03 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ23 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ CZ23 ∷ []) (Sw01 ∷ CZ23 ∷ CS13 ∷ Sw01 ∷ [])
  b0 = at 2 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ CZ23 ∷ []) (sym (low-comm (Swap) (CZ))) ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ23 ∷ CS13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (CZ ↑)) ((CZ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (Sw01 ∷ CZ23 ∷ CS13 ∷ Sw01 ∷ []) (CZ23 ∷ CS03 ∷ [])
  b1 = at 0 2 (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ)) ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03] [CCZ123]: 1 steps
lem-pass-CS03-vs-CCZ123 : ⟪ (CS03 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CCZ123 = run b0
  where
  b0 : Chain (CS03 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03 ∷ [])
  b0 = at 0 2 (CCZ123 ∷ CS03 ∷ []) (sym lem-pass-CCZ123-vs-CS03) ▸ done


-- pass [CS03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (CS03 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CS03 ∷ CCZ123 ∷ [])
  b0 = at 0 2 (ι ∷ CS03 ∷ []) (lem-pass-CS03-vs-iI) ▸
       at 1 2 (ι ∷ CS03 ∷ []) (lem-pass-CS03-vs-iI) ▸
       at 2 2 (Z1 ∷ CS03 ∷ []) (lem-pass-CS03-vs-Z1) ▸
       at 3 2 (Z2 ∷ CS03 ∷ []) (lem-pass-CS03-vs-Z2) ▸
       at 4 2 (CZ12 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CZ12) ▸
       at 5 2 (Z3 ∷ CS03 ∷ []) (lem-pass-CS03-vs-Z3) ▸
       at 6 2 (CZ13 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CZ13) ▸
       at 7 2 (CZ23 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CZ23) ▸ done

  b1 : Chain (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CS03 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ [])
  b1 = at 8 2 (CCZ123 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CCZ123) ▸ done


-- pass [TOFF012] [iI]: 1 steps
lem-pass-TOFF012-vs-iI : ⟪ (Toff012 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-iI = run b0
  where
  b0 : Chain (Toff012 ∷ ι ∷ []) (ι ∷ Toff012 ∷ [])
  b0 = at 0 2 (ι ∷ Toff012 ∷ []) (win 3 0 complete₃ (Toff • iI) (iI • Toff) tt tt Eq.refl) ▸ done


-- pass [TOFF012] [Z1]: 1 steps
lem-pass-TOFF012-vs-Z1 : ⟪ (Toff012 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z1 = run b0
  where
  b0 : Chain (Toff012 ∷ Z1 ∷ []) (Z1 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Z1 ∷ Toff012 ∷ []) (win 3 0 complete₃ (Toff • (Z ↑)) ((Z ↑) • Toff) tt tt Eq.refl) ▸ done


-- pass [TOFF012] [Z2]: 1 steps
lem-pass-TOFF012-vs-Z2 : ⟪ (Toff012 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z2 = run b0
  where
  b0 : Chain (Toff012 ∷ Z2 ∷ []) (Z2 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Z2 ∷ Toff012 ∷ []) (win 3 0 complete₃ (Toff • (Z ↑ ↑)) ((Z ↑ ↑) • Toff) tt tt Eq.refl) ▸ done


-- pass [TOFF012] [CZ12]: 1 steps
lem-pass-TOFF012-vs-CZ12 : ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CZ12 = run b0
  where
  b0 : Chain (Toff012 ∷ CZ12 ∷ []) (CZ12 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CZ12 ∷ Toff012 ∷ []) (win 3 0 complete₃ (Toff • (CZ ↑)) ((CZ ↑) • Toff) tt tt Eq.refl) ▸ done


-- pass [TOFF012] [Z3]: 1 steps
lem-pass-TOFF012-vs-Z3 : ⟪ (Toff012 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z3 = run b0
  where
  b0 : Chain (Toff012 ∷ Z3 ∷ []) (Z3 ∷ Toff012 ∷ [])
  b0 = at 0 2 (Z3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (Z)) ▸ done

