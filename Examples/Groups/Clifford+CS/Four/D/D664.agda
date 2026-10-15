{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D664 where

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
open import Examples.Groups.Clifford+CS.Four.D.D072 using (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D073 using (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D281 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D286 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D348 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D350 using (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D420 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D422 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2)
open import Examples.Groups.Clifford+CS.Four.D.D439 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D441 using (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D611 using (lem-pass-CCZ123-vs-X2-CK21-X2 ; lem-pass-CCZ123-vs-X2-CS12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D613 using (lem-pass-CCZ123-vs-X2-CKd21-X2 ; lem-pass-CCZ123-vs-X2-CSd12-X2)
open import Examples.Groups.Clifford+CS.Four.D.D648 using (lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D650 using (lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D661 using (lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 ; lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 ; lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D663 using (lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3)
-- pass [CKd21] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CKd21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CK21⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = run b0
  where
  b0 : Chain (CK21⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 11 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 9 4 (X2 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 8 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [X2 CS21 X2] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 7 steps
lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 4 (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 3 (X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 4 (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CS • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CS21] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CS21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CS12 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = run b0
  where
  b0 : Chain (CS12 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS12 ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 11 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 9 4 (X2 ∷ CS12 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 8 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [X2 CK21 X2] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 7 steps
lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = run b0
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b0 = at 0 4 (X0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 2 3 (X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 3 (X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 4 (X0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 4 (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CK₁₀ • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CK21] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CK21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CK21 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = run b0
  where
  b0 : Chain (CK21 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21 ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 11 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 9 4 (X2 ∷ CK21 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 8 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- ca-split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1) 2: 31 steps
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩-2 : ⟪ (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩-2 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (K1 ∷ S1 ∷ X0 ∷ S1 ∷ X2 ∷ X3 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (K1 ∷ X3 ∷ []) (sym (low-comm ((K ↑)) ((X ↑)))) ▸
       at 1 2 (K1 ∷ X2 ∷ []) (sym (low-comm ((K ↑)) (X))) ▸
       at 0 2 (K1 ∷ X0 ∷ []) (low₁-comm (X) (K)) ▸
       at 3 2 (S1 ∷ X3 ∷ []) (sym (low-comm ((S ↑)) ((X ↑)))) ▸
       at 2 2 (S1 ∷ X2 ∷ []) (sym (low-comm ((S ↑)) (X))) ▸
       at 1 2 (S1 ∷ X0 ∷ []) (low₁-comm (X) (S)) ▸
       at 4 2 (S1 ∷ X3 ∷ []) (sym (low-comm ((S ↑)) ((X ↑)))) ▸
       at 3 2 (S1 ∷ X2 ∷ []) (sym (low-comm ((S ↑)) (X))) ▸ done

  b1 : Chain (K1 ∷ S1 ∷ X0 ∷ S1 ∷ X2 ∷ X3 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 2 2 (S1 ∷ X0 ∷ []) (low₁-comm (X) (S)) ▸
       at 5 2 (K1⁻ ∷ X3 ∷ []) (sym (low-comm (((K • iI) ↑)) ((X ↑)))) ▸
       at 4 2 (K1⁻ ∷ X2 ∷ []) (sym (low-comm (((K • iI) ↑)) (X))) ▸
       at 3 2 (K1⁻ ∷ X0 ∷ []) (low₁-comm (X) ((K • iI))) ▸
       at 14 2 (X0 ∷ K1⁻ ∷ []) (sym (low₁-comm (X) ((K • iI)))) ▸
       at 13 2 (X0 ∷ S1⁻ ∷ []) (sym (low₁-comm (X) ((S • S • S)))) ▸
       at 12 2 (X0 ∷ S1⁻ ∷ []) (sym (low₁-comm (X) ((S • S • S)))) ▸
       at 11 2 (X0 ∷ K1 ∷ []) (sym (low₁-comm (X) (K))) ▸ done

  b2 : Chain (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ [])
  b2 = at 15 2 (X2 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (X)) ▸
       at 14 2 (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X)) ▸
       at 13 2 (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X)) ▸
       at 12 2 (X2 ∷ K1 ∷ []) (low-comm ((K ↑)) (X)) ▸
       at 16 2 (X3 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) ((X ↑))) ▸
       at 15 2 (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑))) ▸
       at 14 2 (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑))) ▸
       at 13 2 (X3 ∷ K1 ∷ []) (low-comm ((K ↑)) ((X ↑))) ▸ done

  b3 : Chain (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b3 = at 0 4 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((K ↑) • (S ↑) • (S ↑) • ((K • iI) ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 26 4 (CK21 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((K ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • ((K • iI) ↑)) ((CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 15 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) (lem-pass-CKd21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 14 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 13 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 12 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21 ∷ []) (lem-pass-CK21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 22 8 [] (win 3 0 complete₃ ((CK₁₀ ↑) • (CS ↑) • (CS ↑) • ((S ↑ • CK₁₀) ↑) • (CK₁₀ ↑) • ((CS • CS • CS) ↑) • ((CS • CS • CS) ↑) • ((S ↑ • CK₁₀) ↑)) (ε) tt tt Eq.refl) ▸ done


-- Bar(SSKSKK;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 32 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2) ▸
       at 3 32 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2) ▸
       at 6 32 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS12-X2) ▸
       at 9 32 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2) ▸
       at 12 39 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 22 32 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-X2) ▸
       at 25 32 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2) ▸
       at 28 32 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-X2) ▸ done

  b1 : Chain (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b1 = at 31 32 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd21-X2) ▸ done


-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = run b0
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  b0 = at 29 18 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩-2) ▸
       at 0 63 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (lem-Bar⟨SSKSKK23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩) ▸
       at 0 34 (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩-2) ▸ done


-- pass [X2 CKd23 X2] [X0 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X3]: 9 steps
lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X0 ∷ X3 ∷ [])
  b0 = at 0 5 (X0 ∷ X3 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 19 (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • K • S • S • (K • iI)) (K • S • S • (K • iI) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 18 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 15 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 12 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 9 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 19 (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b1 = at 14 17 (X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd23] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 7 steps
lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (CK23⁻ ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23⁻ ∷ []) ⟫ʷ
lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = run b0
  where
  b0 : Chain (CK23⁻ ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23⁻ ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ (((S • CK₀₁) ↑) • (X ↑)) ((X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 19 (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3) ▸
       at 17 4 (X2 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑)) ((X ↑) • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 16 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- CCZ(2,1,3) passes split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1): 9 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK21-X2) ▸
       at 3 4 (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS12-X2) ▸
       at 6 4 (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS12-X2) ▸
       at 9 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd21-X2) ▸
       at 12 11 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 22 4 (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK21-X2) ▸
       at 25 4 (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd12-X2) ▸
       at 28 4 (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd12-X2) ▸ done

  b1 : Chain (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b1 = at 31 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd21-X2) ▸ done


-- pass [CCZ123] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 1 18 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩-2) ▸
       at 0 35 (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩) ▸
       at 0 34 (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩-2) ▸ done


-- pass [X2 CK23 X2] [X0 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X3]: 9 steps
lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK23 ∷ X2 ∷ X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ [])
  b0 = at 0 5 (X0 ∷ X3 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 2 19 (K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • K • S • S • (K • iI)) (K • S • S • (K • iI) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 18 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 15 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 12 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 9 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 10 19 (K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • K • (S • S • S) • (S • S • S) • (K • iI)) (K • (S • S • S) • (S • S • S) • (K • iI) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  b1 = at 14 17 (X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (win 1 2 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CK23] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 7 steps
lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (CK23 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = run b0
  where
  b0 : Chain (CK23 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23 ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • (X ↑)) ((X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 19 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 19 (X0 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3) ▸
       at 17 4 (X2 ∷ CK23 ∷ []) (win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑)) ((X ↑) • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 16 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [TOFF312] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = run b0
  where
  b0 : Chain (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ [])
  b0 = at 0 1 (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ (Toffᵗ) ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 2 19 (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23⁻ ∷ []) (lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3) ▸
       at 1 19 (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3) ▸
       at 0 19 (X0 ∷ X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23 ∷ []) (lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3) ▸
       at 18 3 (Toff312 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done


-- Bar(SSSKSS;2,3->0) passes split Gad(t=1, W=(0, 2, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡KSSKd-e≡1⟩ = trans (run b0) (run b1)
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  b0 = at 0 34 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2) ▸
       at 3 34 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2) ▸
       at 6 34 (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-X2) ▸
       at 9 34 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2) ▸
       at 12 41 (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3) ▸
       at 22 34 (X2 ∷ CK21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-X2) ▸
       at 25 34 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2) ▸
       at 28 34 (X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-X2) ▸ done

  b1 : Chain (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  b1 = at 31 34 (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) (lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2) ▸ done

