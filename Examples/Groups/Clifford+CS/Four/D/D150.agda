{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D150 where

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
open import Examples.Groups.Clifford+CS.Four.D.D046 using (lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 ; lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 ; lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D057 using (lem-pass-X2-CSd20-X2-vs-CS13 ; lem-pass-X2-CSd20-X2-vs-CSd13 ; lem-pass-X2-CSd20-X2-vs-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D073 using (lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D074 using (lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D088 using (lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
-- b2g 0111R1: 4 steps
lem-b2g-0111R1 : ⟪ (X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-0111R1 = run b0
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 1 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 2 3 (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (win 3 0 complete₃ ((X ↑) • (S ↑) • (K ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 10 3 (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (win 3 0 complete₃ (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CS21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ Toff102 ∷ [])
  b0 = at 0 0 (CS13 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 2 0 (CS13⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 4 7 (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b1 = at 7 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CS21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 1 3 (X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 3 (X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CS21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS12 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = run b0
  where
  b0 : Chain (CS12 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS12 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 9 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3) ▸
       at 7 4 (X2 ∷ CS12 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [X2 CKd21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ Toff102 ∷ Toff102 ∷ [])
  b0 = at 0 0 (CS13 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 2 0 (CS13⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 4 7 (X2 ∷ CK21⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ Toff102 ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b1 = at 7 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CKd21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = run b0
  where
  b0 : Chain (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 1 3 (X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 3 (X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CK21⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = run b0
  where
  b0 : Chain (CK21⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 9 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3) ▸
       at 7 4 (X2 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [X2 CSd21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ Toff102 ∷ [])
  b0 = at 0 0 (CS13 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 1 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 2 0 (CS13⁻ ∷ CS13 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 3 0 (Toff102 ∷ Toff102 ∷ []) (win 3 0 complete₃ (ε) ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸
       at 4 7 (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CS • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸
       at 8 2 [] (win 0 3 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b1 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b1 = at 7 2 [] (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • (K ↑ • CCZ • K ↑ • iI)) (ε) tt tt Eq.refl) ▸ done


-- pass [X2 CSd21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 1 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS12⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = run b0
  where
  b0 : Chain (CS12⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS12⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 9 (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3) ▸
       at 7 4 (X2 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- ca-split Gad(t=1, W=(2, 3), d=SdKdSS, e=-1) 2: 23 steps
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (S1⁻ ∷ X3 ∷ []) (sym (low-comm (((S • S • S) ↑)) ((X ↑)))) ▸
       at 0 2 (S1⁻ ∷ X2 ∷ []) (sym (low-comm (((S • S • S) ↑)) (X))) ▸
       at 2 2 (K1⁻ ∷ X3 ∷ []) (sym (low-comm (((K • iI) ↑)) ((X ↑)))) ▸
       at 1 2 (K1⁻ ∷ X2 ∷ []) (sym (low-comm (((K • iI) ↑)) (X))) ▸
       at 3 2 (S1 ∷ X3 ∷ []) (sym (low-comm ((S ↑)) ((X ↑)))) ▸
       at 2 2 (S1 ∷ X2 ∷ []) (sym (low-comm ((S ↑)) (X))) ▸
       at 4 2 (S1 ∷ X3 ∷ []) (sym (low-comm ((S ↑)) ((X ↑)))) ▸
       at 3 2 (S1 ∷ X2 ∷ []) (sym (low-comm ((S ↑)) (X))) ▸ done

  b1 : Chain (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ [])
  b1 = at 13 2 (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X)) ▸
       at 12 2 (X2 ∷ K1 ∷ []) (low-comm ((K ↑)) (X)) ▸
       at 11 2 (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X)) ▸
       at 10 2 (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X)) ▸
       at 14 2 (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑))) ▸
       at 13 2 (X3 ∷ K1 ∷ []) (low-comm ((K ↑)) ((X ↑))) ▸
       at 12 2 (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑))) ▸
       at 11 2 (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑))) ▸ done

  b2 : Chain (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b2 = at 0 4 (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 24 4 (CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 15 9 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3) ▸
       at 14 9 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3) ▸
       at 13 9 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) (lem-pass-CKd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3) ▸
       at 12 9 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS12⁻ ∷ []) (lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3) ▸
       at 20 8 [] (win 3 0 complete₃ (((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (CS ↑) • (CS ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • (CK₁₀ ↑) • (CS ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS13 TOFF102 CSd13 TOFF102] [S0 CSd03 X2 TOFF012 X2 Sd0 CS03 X2 TOFF012 X2]: 4 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = run b0
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 3 11 (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2) ▸
       at 2 11 (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2) ▸
       at 1 11 (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2) ▸
       at 0 11 (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2) ▸ done


-- pass [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 139 steps
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 8 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ [])
  b1 = at 9 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 11 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b2 = at 10 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 6 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b3 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b3 = at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b4 = at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 8 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸ done

  b5 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ X3 ∷ [])
  b5 = at 14 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 13 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b6 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b6 = at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 14 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 13 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ []) (X2 ∷ S0 ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b7 = at 2 14 (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2) ▸
       at 1 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸ done

  b8 : Chain (X2 ∷ S0 ∷ S0⁻ ∷ Sw23 ∷ CS02 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X3 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b8 = at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 5 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 5 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 7 2 (S0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑ ↑)))) ▸ done

  b9 : Chain (X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X3 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b9 = at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (S0 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b10 = at 10 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 11 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 12 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 0 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 1 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b11 : Chain (S0 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (S0 ∷ S0⁻ ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b11 = at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 3 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (S0 ∷ S0⁻ ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b12 = at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 3 4 (Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) (Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 4 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸ done

  b13 : Chain (S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ Sw01 ∷ X2 ∷ CS13⁻ ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b13 = at 5 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸ done

  b14 : Chain (S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ Sw01 ∷ X2 ∷ CS13⁻ ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b14 = at 7 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b15 : Chain (S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b15 = at 7 4 (Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) (Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 1 3 (CS02 ∷ []) (win 3 0 complete₃ (S • (S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b16 : Chain (Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b16 = at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 3 3 (CS02⁻ ∷ []) (win 3 0 complete₃ ((S • S • S) • S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done

  b17 : Chain (CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b17 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 12 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 4 16 (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2) ▸
       at 0 7 (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 3 7 (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 12 12 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3) ▸
       at 20 7 (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 23 7 (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b1 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 26 7 (X2 ∷ CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 29 7 (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 0 32 (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-2) ▸ done


-- pass [X2 CSd20 X2] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS13 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS13) ▸
       at 1 4 (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF102) ▸
       at 2 4 (CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CSd13) ▸
       at 3 4 (Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-TOFF102) ▸ done

