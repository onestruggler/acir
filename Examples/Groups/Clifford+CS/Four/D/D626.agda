{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D626 where

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
open import Examples.Groups.Clifford+CS.Four.D.D068 using (lem-S2-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D621 using (lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1)
open import Examples.Groups.Clifford+CS.Four.D.D623 using (lem-pass-CKd13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 ; lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D624 using (lem-pass-CCZ123-vs-X1-CK10-X1 ; lem-pass-CCZ123-vs-X1-CS01-X1)
open import Examples.Groups.Clifford+CS.Four.D.D625 using (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123)
-- pass [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3] [CCZ123]: 76 steps
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123 : ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (X1 ∷ X2 ∷ X3 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 9 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 10 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (Z2 ∷ CZ12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 12 2 (Z3 ∷ CZ13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CZ • Swap ↑)) ((Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 14 2 (CZ23 ∷ CCZ123 ∷ X1 ∷ []) (win 0 3 complete₃ (X • CCZ) ((CZ ↑) • CCZ • X) tt tt Eq.refl) ▸
       at 3 13 (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123) ▸ done

  b1 : Chain (X1 ∷ X2 ∷ X3 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ X3 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b1 = at 3 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 2 2 (ι3 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 4 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 3 2 (ι3 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (iI ↑ ↑)) ((iI ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 4 2 (Z1 ∷ X3 ∷ []) (sym (low-comm ((Z ↑)) ((X ↑)))) ▸
       at 5 2 (Z2 ∷ X3 ∷ []) (sym (low₃-comm ((Z ↑ ↑)) (X))) ▸ done

  b2 : Chain (X1 ∷ X2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ X3 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ ι ∷ X2 ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b2 = at 6 2 (CZ12 ∷ X3 ∷ []) (sym (low₃-comm ((CZ ↑)) (X))) ▸
       at 7 2 (ι3 ∷ ι3 ∷ Z3 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Z ↑ ↑)) ((iI ↑ ↑) • (iI ↑ ↑) • (Z ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 8 1 (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI)))) ▸
       at 10 2 (Z1 ∷ CZ13 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CZ • Swap ↑)) (Z • (Swap ↑ • CZ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 12 2 (Z2 ∷ CZ23 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 14 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (X1 ∷ ι ∷ X2 ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ X2 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b3 = at 2 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 4 2 (ι ∷ ι ∷ Z2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Z ↑ ↑)) (iI • iI • (Z ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (Z3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (Z)) ▸
       at 12 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸ done

  b4 : Chain (X1 ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ X2 ∷ CZ13 ∷ Z2 ∷ CZ23 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b4 = at 13 2 (CZ13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ ι ∷ Z2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Z ↑ ↑)) (iI • iI • (Z ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 17 2 (Z3 ∷ CZ23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 21 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 2 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b5 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ ι ∷ ι ∷ Z2 ∷ Z1 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ X1 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b5 = at 5 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 6 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 7 2 (Z2 ∷ X1 ∷ []) (low-comm ((X ↑)) (Z)) ▸
       at 8 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 11 2 (Z2 ∷ CZ12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 15 2 (Z3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((Z ↑))) ▸ done

  b6 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ X1 ∷ Z1 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b6 = at 16 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 2 (Z3 ∷ CZ13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CZ • Swap ↑)) ((Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 21 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 22 2 (ι ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • iI) (iI • (X ↑)) tt tt Eq.refl) ▸
       at 23 2 (Z2 ∷ X1 ∷ []) (low-comm ((X ↑)) (Z)) ▸
       at 24 2 (Z3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((Z ↑))) ▸
       at 25 2 (CZ23 ∷ X1 ∷ []) (low-comm ((X ↑)) (CZ)) ▸
       at 26 2 (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Z ↑)) (iI • iI • (Z ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ Z1 ∷ ι ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ X1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b7 = at 29 2 (Z2 ∷ CZ12 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (CZ ↑)) ((Z ↑ ↑) • (CZ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 31 2 (Z3 ∷ CZ13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CZ • Swap ↑)) ((Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 33 2 (CZ23 ∷ CCZ123 ∷ X1 ∷ []) (win 0 3 complete₃ (X • CCZ) ((CZ ↑) • CCZ • X) tt tt Eq.refl) ▸
       at 0 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 1 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 2 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 3 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 5 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸ done

  b8 : Chain (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι ∷ Z2 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι ∷ ι ∷ Z3 ∷ ι ∷ ι ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι3 ∷ Z2 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι3 ∷ ι3 ∷ Z3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι3 ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b8 = at 6 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 8 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 9 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 13 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 14 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 16 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 17 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 21 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸ done

  b9 : Chain (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι3 ∷ Z2 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι3 ∷ ι3 ∷ Z3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι3 ∷ ι ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b9 = at 22 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 26 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 27 1 (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑))))) ▸
       at 0 35 (CCZ123 ∷ []) (win 0 3 complete₃ ((iI ↑ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (iI ↑ ↑) • (iI ↑ ↑) • (Z ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (Z ↑) • CZ • (iI ↑ ↑) • (iI ↑ ↑) • (Z ↑ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • (iI ↑ ↑) • (iI ↑ ↑) • (Z ↑) • (Z ↑ ↑) • (CZ ↑) • (iI ↑ ↑) • (iI ↑ ↑) • Z • (Z ↑) • CZ • (Z ↑ ↑) • (Swap ↑ • CZ • Swap ↑) • (CZ ↑) • CCZ) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 11 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123) ▸ done


-- pass [CCZ123] [X1 CKd10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CKd10-X1 : ⟪ (CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CKd10-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CK10⁻ ∷ CX23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 4 (X1 ∷ CK10⁻ ∷ X1 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CK10⁻ ∷ CX23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 4 (X1 ∷ CK10⁻ ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CK10⁻ ∷ Sw23 ∷ []) (sym (low-comm ((S ↑ • CK₁₀)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 4 (X1 ∷ CK10⁻ ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X1 CSd01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CSd01-X1 : ⟪ (CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CSd01-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ [])
  b0 = at 0 1 (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (win 0 3 complete₃ (CCZ) (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) tt tt Eq.refl) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 2 (CS01⁻ ∷ CX23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CX₀₁))) ▸
       at 6 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 5 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ [])
  b1 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 4 (X1 ∷ CS01⁻ ∷ X1 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 5 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS12 ∷ CS13 ∷ CX23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b2 = at 7 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 3 2 (CS01⁻ ∷ CX23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CX₀₁))) ▸
       at 4 2 (X1 ∷ CX23 ∷ []) (sym (low-comm ((X ↑)) (CX₀₁))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap)) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (CS12 ∷ CS13 ∷ Sw23 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ [])
  b3 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 4 (X1 ∷ CS01⁻ ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 2 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS12 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CS13 ∷ Sw23 ∷ Sw23 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ [])
  b4 = at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 4 (X1 ∷ CS01⁻ ∷ X1 ∷ CS12 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 3 5 (CCZ123 ∷ []) (win 0 3 complete₃ (CS • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (CX₀₁ ↑)) (CCZ) tt tt Eq.refl) ▸ done


-- CCZ(1,2,3) passes split Gad(t=0, W=(1, 2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩ = run b0
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CS01-X1) ▸
       at 3 4 (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CK10-X1) ▸
       at 6 11 (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3) ▸
       at 16 4 (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CKd10-X1) ▸
       at 19 4 (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-CSd01-X1) ▸ done


-- pass [CCZ123] [X1 X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X1 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 1 14 (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1) ▸
       at 0 23 (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) (lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩) ▸
       at 0 22 (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡0-W≡⟨1-2-3⟩-d≡SK-e≡-1⟩-1) ▸ done


-- pass [X1 CKd13 X1] [CS02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CS02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS02 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 2 2 (CS02 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) (Swap • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01 ∷ CK23⁻ ∷ []) (sym (low-comm (CS) ((S • CK₀₁)))) ▸
       at 3 2 (Sw12 ∷ CK13⁻ ∷ []) (win 0 3 complete₃ (((S • CK₀₁) ↑) • Swap) (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02 ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [X1 CKd13 X1] [TOFF013]: 65 steps
lem-pass-X1-CKd13-X1-vs-TOFF013 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF013 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ [])
  b1 = at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b2 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ [])
  b2 = at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Toff012 ∷ Sw23 ∷ [])
  b3 = at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 4 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 0 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b4 : Chain (Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Toff012 ∷ Sw23 ∷ []) (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b4 = at 1 4 (Toff012 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • Toff) (Toff • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b5 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ [])
  b6 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b7 : Chain (Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ Sw23 ∷ [])
  b7 = at 8 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b8 : Chain (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ Sw23 ∷ []) (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b8 = at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [X1 CKd13 X1] [CSd02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CSd02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CSd02 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 2 2 (CS02⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap) (Swap • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 2 2 (CS01⁻ ∷ CK23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((S • CK₀₁)))) ▸
       at 3 2 (Sw12 ∷ CK13⁻ ∷ []) (win 0 3 complete₃ (((S • CK₀₁) ↑) • Swap) (Swap • (Swap ↑ • (S • CK₀₁) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS02⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [X1 CKd13 X1] [CS02 TOFF013 CSd02 TOFF013]: 4 steps
lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS02) ▸
       at 1 4 (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF013) ▸
       at 2 4 (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CSd02) ▸
       at 3 4 (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-TOFF013) ▸ done


-- pass [X1 CKd13 X1] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = run b0
  where
  b0 : Chain (X1 ∷ CK13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  b0 = at 3 4 (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (lem-S2-ᵖ-1) ▸
       at 0 7 (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS02-TOFF013-CSd02-TOFF013) ▸
       at 0 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-ᵖ-1) ▸ done


-- pass [X1 CK13 X1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 101 steps
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (X1 ∷ CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 5 (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 17 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 16 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 13 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 10 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b2 : Chain (X2 ∷ X3 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b2 = at 7 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 6 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 4 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b3 : Chain (X2 ∷ X3 ∷ Sw23 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ S0 ∷ K0 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b3 = at 3 17 (S0 ∷ K0 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • S • K) (S • K • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 4 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 7 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b4 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b4 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 10 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b5 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ Sw23 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  b5 = at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b6 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b6 = at 16 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 13 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13 ∷ X1 ∷ []) (lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 4 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 24 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 23 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸ done

  b7 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b7 = at 22 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 20 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 19 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 18 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b8 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b8 = at 16 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 13 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸ done

  b9 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b9 = at 10 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 9 17 (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) (win 3 0 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 8 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 9 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 10 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b10 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b10 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 13 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 16 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b11 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12 ∷ X1 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b11 = at 19 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 17 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 19 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 22 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸ done

  b12 : Chain (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ CS13 ∷ X1 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ X1 ∷ Sw23 ∷ CS12⁻ ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  b12 = at 25 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 23 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 25 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 17 (X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • CS • Swap ↑) • X • X • (Swap ↑ • (S • CK₀₁) • Swap ↑) • X • X • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X • (X ↑) • (X ↑ ↑)) ((X ↑) • (X ↑ ↑) • X • (Swap ↑ • CK₀₁ • Swap ↑) • X) tt tt Eq.refl) ▸ done


-- pass [CK13] [X1 X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X1 X2 X3]: 7 steps
lem-pass-CK13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : ⟪ (CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CK13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = run b0
  where
  b0 : Chain (CK13 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13 ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • X) (X • X • (Swap ↑ • CK₀₁ • Swap ↑) • X) tt tt Eq.refl) ▸
       at 14 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 15 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 15 (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3) ▸
       at 13 4 (X1 ∷ CK13 ∷ []) (win 0 3 complete₃ (X • (Swap ↑ • CK₀₁ • Swap ↑) • X • X) (X • (Swap ↑ • CK₀₁ • Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 11 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done


-- pass [TOFF312] [X1 X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X1 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 : ⟪ (Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3 = run b0
  where
  b0 : Chain (Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ [])
  b0 = at 0 1 (CK13 ∷ CCZ123 ∷ CK13⁻ ∷ []) (win 0 3 complete₃ (Toffᵗ) ((Swap ↑ • CK₀₁ • Swap ↑) • CCZ • (Swap ↑ • (S • CK₀₁) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 15 (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13⁻ ∷ []) (lem-pass-CKd13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3) ▸
       at 1 15 (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3) ▸
       at 0 15 (X1 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK13 ∷ []) (lem-pass-CK13-vs-X1-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X1-X2-X3) ▸
       at 14 3 (Toff312 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CK₀₁ • Swap ↑) • CCZ • (Swap ↑ • (S • CK₀₁) • Swap ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done


-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 CS01 X1]: 119 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-X1 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-X1 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b0 = at 34 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 33 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 32 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 31 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b1 = at 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b2 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b2 = at 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b3 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b3 = at 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b4 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b4 = at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b5 = at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ [])
  b6 = at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 4 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 3 2 (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap)) ▸ done

  b7 : Chain (CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X1 ∷ CS01 ∷ X1 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ [])
  b7 = at 2 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 0 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 1 34 (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (win 3 0 complete₃ (CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑) • CS • (X ↑)) ((X ↑) • CS • (X ↑) • CS • CS • CS • CK₁₀ • CS • CS • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (S ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (CX₀₁ ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 1 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 2 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 3 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b8 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ Sw23 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ [])
  b8 = at 4 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 5 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 6 2 (CK10 ∷ Sw23 ∷ []) (sym (low-comm (CK₁₀) (Swap))) ▸
       at 7 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b9 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ [])
  b9 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b10 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ [])
  b10 = at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 16 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 18 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ [])
  b11 = at 21 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 21 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 24 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 22 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ [])
  b12 = at 25 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 23 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 24 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 25 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ [])
  b13 = at 29 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 27 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 28 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 31 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 29 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 32 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 30 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  b14 = at 33 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 31 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 34 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 32 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 35 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 33 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

