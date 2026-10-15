{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D658 where

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
open import Examples.Groups.Clifford+CS.Four.D.D017 using (lem-S2-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D070 using (lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D167 using (lem-LF-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20-at-3)
open import Examples.Groups.Clifford+CS.Four.D.D219 using (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS12)
open import Examples.Groups.Clifford+CS.Four.D.D220 using (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd12)
open import Examples.Groups.Clifford+CS.Four.D.D234 using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12)
open import Examples.Groups.Clifford+CS.Four.D.D235 using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12)
open import Examples.Groups.Clifford+CS.Four.D.D478 using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D634 using (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D644 using (lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3)
open import Examples.Groups.Clifford+CS.Four.D.D645 using (lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3)
open import Examples.Groups.Clifford+CS.Four.D.D647 using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123 ; lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D657 using (lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 ; lem-pass-X3-CKd32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0)
-- pass [CKd32] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 5 steps
lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (CK32⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32⁻ ∷ []) ⟫ʷ
lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = run b0
  where
  b0 : Chain (CK32⁻ ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32⁻ ∷ [])
  b0 = at 1 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 0 2 (X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (win 0 3 complete₃ (((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 9 (X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0) ▸
       at 7 4 (X3 ∷ CK32⁻ ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done


-- pass [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3] [CCZ123]: 10 steps
lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-CCZ123 : ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (CZ12 ∷ CZ12 ∷ X0 ∷ CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ [])
  b0 = at 7 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ)) ▸
       at 7 2 (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ)) ▸
       at 2 6 (CZ12 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CZ12-CCZ123) ▸
       at 1 2 (CZ12 ∷ X3 ∷ []) (sym (low₃-comm ((CZ ↑)) (X))) ▸
       at 2 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ)) ▸
       at 1 2 (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ)) ▸ done

  b1 : Chain (CZ12 ∷ CZ12 ∷ X0 ∷ CCZ123 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ [])
  b1 = at 2 2 (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ)) ▸
       at 0 3 (CCZ123 ∷ []) (win 0 3 complete₃ (CZ • CZ • CCZ) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 9 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-CCZ123) ▸ done


-- CCZ(3,1,2) passes split Gad(t=1, W=(0, 3), d=1, e=1): 1 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩ = run b0
  where
  b0 : Chain (CCZ123 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 9 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸ done


-- pass [X3 CK32 X3] [X0 TOFF102 CS13 TOFF102 CSd13 X0]: 5 steps
lem-pass-X3-CK32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 = run b0
  where
  b0 : Chain (X3 ∷ CK32 ∷ X3 ∷ X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  b0 = at 0 4 (X0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 3 (X3 ∷ CK32 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 3 (X3 ∷ CK32 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 4 (X0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • X) (X • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [CK32] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 5 steps
lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (CK32 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = run b0
  where
  b0 : Chain (CK32 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32 ∷ [])
  b0 = at 1 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 0 2 (X3 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (win 0 3 complete₃ ((CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 9 (X0 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0) ▸
       at 7 4 (X3 ∷ CK32 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X3 ∷ []) (sym (low₁-comm (X) ((X ↑ ↑)))) ▸ done


-- pass [TOFF213] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 5 steps
lem-pass-TOFF213-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (Toff213 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ
lem-pass-TOFF213-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = run b0
  where
  b0 : Chain (Toff213 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff213 ∷ [])
  b0 = at 0 1 (CK32 ∷ CCZ123 ∷ CK32⁻ ∷ []) (win 0 3 complete₃ ((K ↑ • CCZ • K ↑ • iI)) ((CK₁₀ ↑) • CCZ • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 2 9 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32⁻ ∷ []) (lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 1 9 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 0 9 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CK32 ∷ []) (lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 8 3 (Toff213 ∷ []) (win 0 3 complete₃ ((CK₁₀ ↑) • CCZ • ((S ↑ • CK₁₀) ↑)) ((K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸ done


-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 19 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ [])
  b0 = at 33 4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-S2-at1023) ▸
       at 34 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 39 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 44 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 36 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 37 2 (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS)) ▸
       at 38 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 36 2 (CS12 ∷ X3 ∷ []) (sym (low₃-comm ((CS ↑)) (X))) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ [])
  b1 = at 37 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 42 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 43 2 (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS))) ▸
       at 44 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 42 2 (CS12⁻ ∷ X3 ∷ []) (sym (low₃-comm (((CS • CS • CS) ↑)) (X))) ▸
       at 43 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 36 (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3) ▸
       at 5 32 (CS12 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS12) ▸ done

  b2 : Chain (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  b2 = at 6 36 (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3) ▸
       at 11 32 (CS12⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd12) ▸
       at 0 12 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (sym lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12) ▸ done


-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 19 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ [])
  b0 = at 31 4 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-S2-at1023) ▸
       at 32 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 37 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 42 0 (X0 ∷ X3 ∷ X0 ∷ X3 ∷ []) (win 1 2 complete₃ (ε) (X • (X ↑ ↑) • X • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 34 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 35 2 (CS12 ∷ X0 ∷ []) (low₁-comm (X) (CS)) ▸
       at 36 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 34 2 (CS12 ∷ X3 ∷ []) (sym (low₃-comm ((CS ↑)) (X))) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ X3 ∷ X3 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ [])
  b1 = at 35 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 40 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 41 2 (CS12⁻ ∷ X0 ∷ []) (low₁-comm (X) ((CS • CS • CS))) ▸
       at 42 2 [] (win 3 0 complete₃ (X • X) (ε) tt tt Eq.refl) ▸
       at 40 2 (CS12⁻ ∷ X3 ∷ []) (sym (low₃-comm (((CS • CS • CS) ↑)) (X))) ▸
       at 41 2 [] (win 0 3 complete₃ ((X ↑ ↑) • (X ↑ ↑)) (ε) tt tt Eq.refl) ▸
       at 0 34 (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3) ▸
       at 5 30 (CS12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12) ▸ done

  b2 : Chain (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS12⁻ ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  b2 = at 6 34 (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3) ▸
       at 11 30 (CS12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12) ▸
       at 0 12 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (sym lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩-TOFF103-CS12-TOFF103-CSd12) ▸ done


-- far CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 .. 1001PP1 sep 3: 7 steps
lem-far-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-··-1001PP1-sep-3 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ
lem-far-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-··-1001PP1-sep-3 = run b0
  where
  b0 : Chain (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ [])
  b0 = at 0 80 (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-LF-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20-at-3) ▸
       at 62 37 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 61 9 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff213 ∷ []) (lem-pass-TOFF213-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 30 39 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 29 9 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ Toff213 ∷ []) (lem-pass-TOFF213-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 0 37 (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3) ▸
       at 8 91 (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) (sym lem-LF-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20-at-3) ▸ done


-- b2g 1011PP0: 4 steps
lem-b2g-1011PP0 : ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1011PP0 = run b0
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 1 2 (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑))) ▸
       at 2 1 (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (win 3 0 complete₃ (X) (K • S • S • (K • iI)) tt tt Eq.refl) ▸
       at 10 1 (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (win 3 0 complete₃ (X) (K • (S • S • S) • (S • S • S) • (K • iI)) tt tt Eq.refl) ▸ done


-- pass [X2 CKd20 X2] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 1 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b1 : Chain (X3 ∷ X2 ∷ Sw01 ∷ CK21⁻ ∷ X2 ∷ Sw01 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ [])
  b1 = at 2 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 4 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 1 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 5 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸ done

  b2 : Chain (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 6 2 (Sw01 ∷ CK21⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) (Swap • ((S ↑ • CK₁₀) ↑)) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 6 4 (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) tt tt Eq.refl) ▸
       at 5 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 6 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 7 2 (CK20⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((S ↑ • CK₁₀) ↑)) ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw01 ∷ Sw01 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b3 = at 9 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CKd20] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CK20⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = run b0
  where
  b0 : Chain (CK20⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 9 (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3) ▸
       at 7 4 (X2 ∷ CK20⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [CS20] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CS02 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = run b0
  where
  b0 : Chain (CS02 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 9 (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3) ▸
       at 7 4 (X2 ∷ CS02 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [CK20] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CK20 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = run b0
  where
  b0 : Chain (CK20 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 9 (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3) ▸
       at 7 4 (X2 ∷ CK20 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑)) tt tt Eq.refl) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- ca-split Gad(t=0, W=(2, 3), d=KSSKd, e=1) 2: 23 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 : ⟪ (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡KSSKd-e≡1⟩-2 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (K0 ∷ X3 ∷ []) (sym (low₁-comm (K) ((X ↑ ↑)))) ▸
       at 0 2 (K0 ∷ X2 ∷ []) (sym (low₁-comm (K) ((X ↑)))) ▸
       at 2 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 1 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 3 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 2 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 4 2 (K0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((K • iI)) ((X ↑ ↑)))) ▸
       at 3 2 (K0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((K • iI)) ((X ↑)))) ▸ done

  b1 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ [])
  b1 = at 13 2 (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑))) ▸
       at 12 2 (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑))) ▸
       at 11 2 (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑))) ▸
       at 10 2 (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑))) ▸
       at 14 2 (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑))) ▸
       at 13 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 12 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 11 2 (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑))) ▸ done

  b2 : Chain (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  b2 = at 0 4 (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ []) (win 3 0 complete₃ (K • S • S • (K • iI)) ((X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) tt tt Eq.refl) ▸
       at 24 4 (CK20 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (win 3 0 complete₃ (K • (S • S • S) • (S • S • S) • (K • iI)) ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 15 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) (lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 14 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ []) (lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 13 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ []) (lem-pass-CS20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 12 9 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) (lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 20 8 [] (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑)) (ε) tt tt Eq.refl) ▸ done

