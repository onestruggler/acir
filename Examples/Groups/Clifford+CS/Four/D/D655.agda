{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D655 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Windows using (win)
open import Examples.Groups.Clifford+CS.Completeness using (complete₃)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.D.D008 using (lem-S2)
open import Examples.Groups.Clifford+CS.Four.D.D039 using (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D152 using (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D624 using (lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D625 using (lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 ; lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D626 using (lem-pass-X1-CKd13-X1-vs-CS02 ; lem-pass-X1-CKd13-X1-vs-CSd02 ; lem-pass-X1-CKd13-X1-vs-TOFF013)
open import Examples.Groups.Clifford+CS.Four.D.D654 using (lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03)
-- pass [X1 CKd13 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 9 steps
lem-pass-X1-CKd13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 5 (X2 ∷ X3 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X) tt tt Eq.refl) ▸
       at 2 15 (X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X) (X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X) tt tt Eq.refl) ▸
       at 14 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 11 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 8 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 5 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 6 15 (X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X) (X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13 ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b1 = at 6 17 (X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) tt tt Eq.refl) ▸ done


-- pass [CKd13] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CKd13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13⁻ ∷ []) ⟫ʷ
lem-pass-CKd13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = run b0
  where
  b0 : Chain (CK13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13⁻ ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S • CK₀₁) • Swap ↑) • X) (X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 11 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 11 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 9 4 (X1 ∷ CK13⁻ ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X) (X • (Swap ↑ • (S • CK₀₁) • Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 7 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [TOFF012 CS03 TOFF012 CSd03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = run b0
  where
  b0 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 3 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸
       at 2 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸
       at 1 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ []) (lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸
       at 0 10 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸ done


-- pass [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3] [CCZ123]: 76 steps
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 : ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (X1 ∷ X2 ∷ X3 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 9 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 10 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (Z2 ∷ CZ12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 12 2 (Z3 ∷ CZ13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CZ • Swap ↑)) ((Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 14 2 (CZ23 ∷ CCZ123 ∷ X1 ∷ []) (win 0 3 complete₃ (X • CCZ) ((CZ ↑) • CCZ • X) tt tt Eq.refl) ▸
       at 3 13 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸ done

  b1 : Chain (X1 ∷ X2 ∷ X3 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ X3 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b1 = at 3 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 2 2 (ι3 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 4 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 3 2 (ι3 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 4 2 (Z1 ∷ X3 ∷ []) (sym (low-comm ((Z ↑)) ((X ↑)))) ▸
       at 5 2 (Z2 ∷ X3 ∷ []) (sym (low₃-comm ((Z ↑ ↑)) (X))) ▸ done

  b2 : Chain (X1 ∷ X2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ X3 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ ι ∷ X2 ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b2 = at 6 2 (CZ12 ∷ X3 ∷ []) (sym (low₃-comm ((CZ ↑)) (X))) ▸
       at 7 2 (ι3 ∷ ι3 ∷ Z3 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Z ↑ ↑)) ((iI ↑ ↑) • (iI ↑ ↑) • (Z ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 8 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 10 2 (Z1 ∷ CZ13 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CZ • Swap ↑)) (Z • (Swap ↑ • CZ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 12 2 (Z2 ∷ CZ23 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 14 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (X1 ∷ ι ∷ X2 ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ X2 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b3 = at 2 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 4 2 (ι ∷ ι ∷ Z2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Z ↑ ↑)) (iI • iI • (Z ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (Z3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (Z)) ▸
       at 12 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸ done

  b4 : Chain (X1 ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ X2 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b4 = at 13 2 (CZ13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ ι ∷ Z2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Z ↑ ↑)) (iI • iI • (Z ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 17 2 (Z3 ∷ CZ23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 21 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 2 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ X1 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b5 = at 5 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 6 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 7 2 (Z2 ∷ X1 ∷ []) (low-comm ((X ↑)) (Z)) ▸
       at 8 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 11 2 (Z2 ∷ CZ12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 15 2 (Z3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((Z ↑))) ▸ done

  b6 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ X1 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b6 = at 16 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 2 (Z3 ∷ CZ13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CZ • Swap ↑)) ((Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 21 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 22 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 23 2 (Z2 ∷ X1 ∷ []) (low-comm ((X ↑)) (Z)) ▸
       at 24 2 (Z3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((Z ↑))) ▸
       at 25 2 (CZ23 ∷ X1 ∷ []) (low-comm ((X ↑)) (CZ)) ▸
       at 26 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b7 = at 29 2 (Z2 ∷ CZ12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 31 2 (Z3 ∷ CZ13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CZ • Swap ↑)) ((Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 33 2 (CZ23 ∷ CCZ123 ∷ X1 ∷ []) (win 0 3 complete₃ (X • CCZ) ((CZ ↑) • CCZ • X) tt tt Eq.refl) ▸
       at 0 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 1 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 2 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 3 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 5 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸ done

  b8 : Chain (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι3 ∷ Z2 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι3 ∷ ι3 ∷ Z3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι3 ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b8 = at 6 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 8 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 9 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 13 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 14 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 16 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 17 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 21 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸ done

  b9 : Chain (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι3 ∷ Z2 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι3 ∷ ι3 ∷ Z3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι3 ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b9 = at 22 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 26 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 27 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 0 35 (CCZ123 ∷ []) (win 0 3 complete₃ ((iI ↑ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (iI ↑ ↑) • (iI ↑ ↑) • (Z ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (Z ↑) • CZ • (iI ↑ ↑) • (iI ↑ ↑) • (Z ↑ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • (iI ↑ ↑) • (iI ↑ ↑) • (Z ↑) • (Z ↑ ↑) • (CZ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (Z ↑) • CZ • (Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • (CZ ↑) • CCZ) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 11 (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123) ▸ done


-- CCZ(1,2,3) passes split Gad(t=0, W=(1, 2, 3), d=1, e=1): 1 steps
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡1-e≡1⟩ = run b0
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 11 (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3) ▸ done


-- pass [X1 CKd13 X1] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF013) ▸
       at 1 4 (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS02) ▸
       at 2 4 (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF013) ▸
       at 3 4 (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CSd02) ▸ done


-- pass [X1 CKd13 X1] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 3 4 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2) ▸
       at 0 7 (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF013-CS02-TOFF013-CSd02) ▸
       at 0 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (sym lem-S2) ▸ done


-- pass [X1 CK13 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 9 steps
lem-pass-X1-CK13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 5 (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 2 15 (X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 14 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 11 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 8 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 5 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 2 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 6 15 (X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  b1 = at 6 17 (X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • X • (Swap ↑ • CK₀₁ • Swap ↑) • X) tt tt Eq.refl) ▸ done


-- pass [CK13] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CK13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CK13 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CK13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = run b0
  where
  b0 : Chain (CK13 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13 ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • X) (X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 11 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 11 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 9 4 (X1 ∷ CK13 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X) (X • (Swap ↑ • CK₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 7 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [TOFF312] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = run b0
  where
  b0 : Chain (Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ [])
  b0 = at 0 1 (CK13 ∷ CCZ123 ∷ CK13⁻ ∷ []) (win 0 3 complete₃ (Toffᵗ) ((Swap ↑ • CK₀₁ • Swap ↑) • CCZ • (Swap ↑ • (S • CK₀₁) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 11 (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13⁻ ∷ []) (lem-pass-CKd13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3) ▸
       at 1 11 (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3) ▸
       at 0 11 (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13 ∷ []) (lem-pass-CK13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3) ▸
       at 10 3 (Toff312 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • CCZ • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [X3 CKd30 X3] [X1 X2 TOFF012 CS03 TOFF012 CSd03 X1 X2]: 87 steps
lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b1 : Chain (X1 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X3 ∷ CK30⁻ ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸ done

  b2 : Chain (X1 ∷ X3 ∷ CK30⁻ ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b2 = at 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 4 (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b3 = at 2 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b4 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ [])
  b5 = at 3 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b6 = at 6 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ [])
  b7 = at 9 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 4 (X1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b8 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ [])
  b9 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 4 (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b10 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b10 = at 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CKd30] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 27 steps
lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X3 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 11 (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 11 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 4 (X2 ∷ CK20⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ Sw23 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ [])
  b3 = at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [X1 CSd10 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 2 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 6 3 (X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 6 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 7 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 2 1 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd10] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = run b0
  where
  b0 : Chain (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((CS • CS • CS) • (X ↑)) ((X ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 11 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 11 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 9 4 (X1 ∷ CS01⁻ ∷ []) (win 3 0 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑)) ((X ↑) • (CS • CS • CS)) tt tt Eq.refl) ▸
       at 8 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 7 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [X3 CK30 X3] [X1 X2 TOFF012 CS03 TOFF012 CSd03 X1 X2]: 87 steps
lem-pass-X3-CK30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (X3 ∷ CK30 ∷ X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 4 (X1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b1 : Chain (X1 ∷ Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X3 ∷ CK30 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸ done

  b2 : Chain (X1 ∷ X3 ∷ CK30 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b2 = at 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 4 (X2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X1 ∷ X2 ∷ Sw01 ∷ X3 ∷ CK31 ∷ X3 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b3 = at 2 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 5 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (X1 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ [])
  b4 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 3 (X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (X1 ∷ X2 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ [])
  b5 = at 3 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b6 = at 6 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 3 (X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 7 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X2 ∷ [])
  b7 = at 9 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 4 (X1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b8 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CK31 ∷ X3 ∷ Sw01 ∷ [])
  b9 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 4 (X2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑)) ((X ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b10 : Chain (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Sw01 ∷ CK31 ∷ X3 ∷ Sw01 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  b10 = at 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

