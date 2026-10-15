{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D162 where

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
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CS13-vs-CSd03 ; lem-pass-CS13-vs-S0 ; lem-pass-TOFF102-vs-CS03 ; lem-pass-TOFF102-vs-CSd03 ; lem-pass-TOFF102-vs-S0 ; lem-pass-TOFF102-vs-Sd0 ; lem-pass-TOFF102-vs-X2-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D031 using (lem-pass-CS13-vs-CS03 ; lem-pass-CS13-vs-Sd0 ; lem-pass-CSd13-vs-CS03 ; lem-pass-CSd13-vs-CSd03 ; lem-pass-CSd13-vs-S0 ; lem-pass-CSd13-vs-Sd0 ; lem-pass-CSd13-vs-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D073 using (lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D074 using (lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D134 using (lem-pass-CS13-vs-S3 ; lem-pass-CS13-vs-Sd3 ; lem-pass-CS13-vs-iI)
open import Examples.Groups.Clifford+CS.Four.D.D151 using (lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D161 using (lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2 ; lem-pass-CS13-vs-X2-TOFF012-X2)
-- pass [CS13] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 12 steps
lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (CS13 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ CS13 ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ [])
  b0 = at 0 2 (ι ∷ CS13 ∷ []) (lem-pass-CS13-vs-iI) ▸
       at 1 2 (S0⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-Sd0) ▸
       at 2 2 (S3⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-Sd3) ▸
       at 3 2 (CS03 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS03) ▸
       at 4 4 (X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) (lem-pass-CS13-vs-X2-TOFF012-X2) ▸
       at 7 2 (ι ∷ CS13 ∷ []) (lem-pass-CS13-vs-iI) ▸
       at 8 2 (ι ∷ CS13 ∷ []) (lem-pass-CS13-vs-iI) ▸
       at 9 2 (ι ∷ CS13 ∷ []) (lem-pass-CS13-vs-iI) ▸ done

  b1 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ CS13 ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ [])
  b1 = at 10 2 (S0 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S0) ▸
       at 11 2 (S3 ∷ CS13 ∷ []) (lem-pass-CS13-vs-S3) ▸
       at 12 2 (CS03⁻ ∷ CS13 ∷ []) (lem-pass-CS13-vs-CSd03) ▸
       at 13 4 (X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) (lem-pass-CS13-vs-X2-TOFF012-X2) ▸ done


-- pass [TOFF102] [iI]: 1 steps
lem-pass-TOFF102-vs-iI : ⟪ (Toff102 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-iI = run b0
  where
  b0 : Chain (Toff102 ∷ ι ∷ []) (ι ∷ Toff102 ∷ [])
  b0 = at 0 2 (ι ∷ Toff102 ∷ []) (win 3 0 complete₃ ((K ↑ • CCZ • K ↑ • iI) • iI) (iI • (K ↑ • CCZ • K ↑ • iI)) tt tt Eq.refl) ▸ done


-- pass [TOFF102] [Sd3]: 1 steps
lem-pass-TOFF102-vs-Sd3 : ⟪ (Toff102 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-Sd3 = run b0
  where
  b0 : Chain (Toff102 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff102 ∷ [])
  b0 = at 0 2 (S3⁻ ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) ((S • S • S))) ▸ done


-- pass [TOFF102] [S3]: 1 steps
lem-pass-TOFF102-vs-S3 : ⟪ (Toff102 ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-S3 = run b0
  where
  b0 : Chain (Toff102 ∷ S3 ∷ []) (S3 ∷ Toff102 ∷ [])
  b0 = at 0 2 (S3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (S)) ▸ done


-- pass [TOFF102] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 12 steps
lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ Toff102 ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ [])
  b0 = at 0 2 (ι ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI) ▸
       at 1 2 (S0⁻ ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-Sd0) ▸
       at 2 2 (S3⁻ ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-Sd3) ▸
       at 3 2 (CS03 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-CS03) ▸
       at 4 4 (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-X2-TOFF012-X2) ▸
       at 7 2 (ι ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI) ▸
       at 8 2 (ι ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI) ▸
       at 9 2 (ι ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI) ▸ done

  b1 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ Toff102 ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ [])
  b1 = at 10 2 (S0 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-S0) ▸
       at 11 2 (S3 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-S3) ▸
       at 12 2 (CS03⁻ ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-CSd03) ▸
       at 13 4 (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-X2-TOFF012-X2) ▸ done


-- pass [CSd13] [iI]: 9 steps
lem-pass-CSd13-vs-iI : ⟪ (CS13⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-iI = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ ι ∷ []) (ι ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • iI) (iI • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (ι ∷ CS13⁻ ∷ Sw23 ∷ Sw23 ∷ []) (ι ∷ CS13⁻ ∷ [])
  b1 = at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd13] [Sd3]: 1 steps
lem-pass-CSd13-vs-Sd3 : ⟪ (CS13⁻ ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-Sd3 = run b0
  where
  b0 : Chain (CS13⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS13⁻ ∷ [])
  b0 = at 0 2 (S3⁻ ∷ CS13⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • ((S • S • S) ↑ ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd13] [X2 TOFF012 X2]: 12 steps
lem-pass-CSd13-vs-X2-TOFF012-X2 : ⟪ (CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-X2-TOFF012-X2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (CX10 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ [])
  b0 = at 1 3 (CX10 ∷ Toff012 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff • (X ↑ ↑)) (CX₁₀ • Toff) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (CX10 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • CX₁₀) (CX₁₀ • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (CX10 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ [])
  b1 = at 1 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-TOFF012) ▸
       at 0 2 (X2 ∷ Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ (CX₁₀ • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd13] [S3]: 1 steps
lem-pass-CSd13-vs-S3 : ⟪ (CS13⁻ ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-S3 = run b0
  where
  b0 : Chain (CS13⁻ ∷ S3 ∷ []) (S3 ∷ CS13⁻ ∷ [])
  b0 = at 0 2 (S3 ∷ CS13⁻ ∷ []) (win 0 3 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S ↑ ↑)) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [CSd13] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 12 steps
lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (CS13⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ CS13⁻ ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ [])
  b0 = at 0 2 (ι ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-iI) ▸
       at 1 2 (S0⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-Sd0) ▸
       at 2 2 (S3⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-Sd3) ▸
       at 3 2 (CS03 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CS03) ▸
       at 4 4 (X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-X2-TOFF012-X2) ▸
       at 7 2 (ι ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-iI) ▸
       at 8 2 (ι ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-iI) ▸
       at 9 2 (ι ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-iI) ▸ done

  b1 : Chain (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ CS13⁻ ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (S0 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-S0) ▸
       at 11 2 (S3 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-S3) ▸
       at 12 2 (CS03⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CSd03) ▸
       at 13 4 (X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-X2-TOFF012-X2) ▸ done


-- pass [CS13 TOFF102 CSd13 TOFF102] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 4 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = run b0
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 3 17 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2) ▸
       at 2 17 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2) ▸
       at 1 17 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2) ▸
       at 0 17 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) (lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2) ▸ done


-- pass [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 235 steps
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (run b29)))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 9 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ [])
  b1 = at 11 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b2 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b2 = at 12 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 15 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 14 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 8 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b3 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Sw01 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b3 = at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 10 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ X3 ∷ [])
  b4 = at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 13 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸ done

  b5 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ X3 ∷ [])
  b5 = at 16 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 16 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 16 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 15 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b6 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ Toff012 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b6 = at 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 16 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 16 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 15 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • Toff) ((X ↑ ↑) • Toff • (X ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b7 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b7 = at 7 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (win 3 0 complete₃ (X • S) (iI • (S • S • S) • X) tt tt Eq.refl) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 9 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 10 2 (S2⁻ ∷ CS02 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • X) tt tt Eq.refl) ▸
       at 9 2 (S3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b8 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ [])
  b8 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 12 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 4 (X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • X) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (S • S • S)) (iI • iI • iI • S • X) tt tt Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b9 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b9 = at 18 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 19 2 (S2 ∷ CS02⁻ ∷ X0 ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • CS • Swap ↑)) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 18 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 19 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 21 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 20 4 (X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (X ↑ ↑) • Toff • (X ↑ ↑)) ((X ↑ ↑) • Toff • (X ↑ ↑) • X) tt tt Eq.refl) ▸ done

  b10 : Chain (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ Sw23 ∷ X2 ∷ CS02 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b10 = at 3 20 (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2) ▸
       at 2 2 (ι ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 2 (S0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑ ↑)))) ▸
       at 4 2 (ι ∷ ι ∷ ι ∷ S3 ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • ((S • S • S) ↑ ↑)) (iI • iI • iI • (S ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b11 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ Sw23 ∷ X2 ∷ CS02 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X3 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b11 = at 9 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑)) (S • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 11 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 11 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸ done

  b12 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X3 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b12 = at 12 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 13 2 (ι ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 15 2 (ι ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 16 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 17 2 (ι ∷ S3⁻ ∷ X3 ∷ []) (win 1 2 complete₃ ((X ↑ ↑) • (S ↑ ↑)) (iI • ((S • S • S) ↑ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X3 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b13 = at 22 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 19 2 (Sw23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑)) ((Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 20 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((S • S • S) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 19 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 20 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (X ↑)) ((X ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 22 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b14 : Chain (X0 ∷ X2 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X3 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ X2 ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b14 = at 21 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 22 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 23 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 1 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 2 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 3 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 4 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b15 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ X2 ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ X2 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b15 = at 6 2 (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S)) ▸
       at 7 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 10 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ X2 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b16 = at 8 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 9 2 (CS13⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b17 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Sw01 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b17 = at 10 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 9 4 (Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) (Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 10 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 11 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 12 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 13 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 14 2 (ι ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • iI) (iI • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 15 2 (S3⁻ ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) ((S • S • S))) ▸ done

  b18 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ Sw01 ∷ X2 ∷ CS13 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b18 = at 16 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 19 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 19 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸ done

  b19 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ Sw01 ∷ X2 ∷ CS13 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b19 = at 18 2 (CS13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 19 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done

  b20 : Chain (X0 ∷ ι ∷ S0⁻ ∷ ι ∷ ι ∷ ι ∷ S3 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ X0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b20 = at 18 4 (Toff012 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (X ↑ ↑) • Toff • (X ↑ ↑)) (Toff • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 0 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸
       at 1 2 (ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (S • S • S)) (iI • iI • iI • S • X) tt tt Eq.refl) ▸
       at 5 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸
       at 6 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸
       at 7 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸
       at 8 2 (S3 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑ ↑))) ▸
       at 9 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (win 3 0 complete₃ (X • S) (iI • (S • S • S) • X) tt tt Eq.refl) ▸ done

  b21 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ X0 ∷ CS03⁻ ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b21 = at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 11 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 12 2 (S2⁻ ∷ CS02 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • (CS • CS • CS) • Swap ↑)) (((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑) • X) tt tt Eq.refl) ▸
       at 11 2 (S3⁻ ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • ((S • S • S) ↑)) (((S • S • S) ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Sw23 ∷ X0 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ X0 ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b22 = at 13 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Toff012 ∷ X0 ∷ []) (win 3 0 complete₃ (X • Toff) (Toff • X) tt tt Eq.refl) ▸
       at 14 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸
       at 15 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸
       at 16 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸
       at 17 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (win 3 0 complete₃ (X • S) (iI • (S • S • S) • X) tt tt Eq.refl) ▸
       at 19 2 (ι ∷ X0 ∷ []) (win 3 0 complete₃ (X • iI) (iI • X) tt tt Eq.refl) ▸ done

  b23 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ X0 ∷ S3⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ Sw23 ∷ CS02⁻ ∷ X0 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b23 = at 20 2 (S3⁻ ∷ X0 ∷ []) (low₁-comm (X) (((S • S • S) ↑ ↑))) ▸
       at 21 2 (ι ∷ ι ∷ ι ∷ S0 ∷ X0 ∷ []) (win 3 0 complete₃ (X • (S • S • S)) (iI • iI • iI • S • X) tt tt Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 25 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 26 2 (S2 ∷ CS02⁻ ∷ X0 ∷ []) (win 3 0 complete₃ (X • (Swap ↑ • CS • Swap ↑)) ((S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • X) tt tt Eq.refl) ▸
       at 25 2 (S3 ∷ Sw23 ∷ []) (win 0 3 complete₃ ((Swap ↑) • (S ↑)) ((S ↑ ↑) • (Swap ↑)) tt tt Eq.refl) ▸ done

  b24 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ Sw23 ∷ CS02⁻ ∷ X0 ∷ Sw23 ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b24 = at 28 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 26 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 28 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 27 2 (Toff012 ∷ X0 ∷ []) (win 3 0 complete₃ (X • Toff) (Toff • X) tt tt Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b25 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S3 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (ι ∷ ι ∷ ι ∷ ι ∷ Sw23 ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S2 ∷ ι ∷ S0⁻ ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b25 = at 11 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 10 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸ done

  b26 : Chain (ι ∷ ι ∷ ι ∷ ι ∷ Sw23 ∷ S0 ∷ ι ∷ ι ∷ ι ∷ S2 ∷ ι ∷ S0⁻ ∷ S2⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b26 = at 3 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 1 13 (CS02 ∷ []) (win 3 0 complete₃ (iI • iI • iI • iI • S • iI • iI • iI • (S ↑ ↑) • iI • (S • S • S) • ((S • S • S) ↑ ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done

  b27 : Chain (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ Sw23 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S2 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b27 = at 15 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 13 2 (Sw23 ∷ S2 ∷ []) (win 0 3 complete₃ ((S ↑ ↑) • (Swap ↑)) ((Swap ↑) • (S ↑)) tt tt Eq.refl) ▸
       at 12 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 11 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 10 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 9 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸ done

  b28 : Chain (CS03 ∷ Toff012 ∷ ι ∷ ι ∷ ι ∷ ι ∷ S0⁻ ∷ ι ∷ S3⁻ ∷ Sw23 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S2 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b28 = at 8 2 (Sw23 ∷ S2⁻ ∷ []) (win 0 3 complete₃ (((S • S • S) ↑ ↑) • (Swap ↑)) ((Swap ↑) • ((S • S • S) ↑)) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 5 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 4 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑))) ▸
       at 3 13 (CS02⁻ ∷ []) (win 3 0 complete₃ (iI • iI • iI • iI • (S • S • S) • iI • ((S • S • S) ↑ ↑) • iI • iI • iI • S • (S ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸ done

  b29 : Chain (CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  b29 = at 4 0 (Sw23 ∷ Sw23 ∷ []) (win 0 3 complete₃ (ε) ((Swap ↑) • (Swap ↑)) tt tt Eq.refl) ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (win 0 3 complete₃ ((Swap ↑) • (Swap ↑)) (ε) tt tt Eq.refl) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = run b0
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 14 (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done


-- pass [CS03 TOFF012 CSd03 TOFF012] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 11 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 4 18 (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2) ▸
       at 0 7 (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 3 7 (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 7 (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 9 7 (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 12 14 (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3) ▸
       at 22 7 (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 25 7 (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸ done

  b1 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b1 = at 28 7 (X2 ∷ CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 31 7 (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 0 34 (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩-2) ▸ done


-- pass [X2 CSd20 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 43 steps
lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ Sw01 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ [])
  b0 = at 5 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) (Swap • ((CS • CS • CS) ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 1 5 (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS • CS • CS) • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CK₁₀ • (X ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸ done

  b1 : Chain (X0 ∷ Sw01 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ Sw01 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ Sw01 ∷ CK21 ∷ X2 ∷ Sw01 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 2 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 4 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 6 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b2 : Chain (X0 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ Sw01 ∷ CK21 ∷ X2 ∷ Sw01 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X0 ∷ X3 ∷ [])
  b2 = at 9 2 (CK20 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CK₁₀ ↑)) ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 11 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸
       at 2 13 (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑)) (((S • S • S) ↑) • ((K • iI) ↑) • (S ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 12 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 9 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 6 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 10 13 (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • ((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑)) (((S • S • S) ↑) • ((S • S • S) ↑) • (K ↑) • (S ↑) • (X ↑ ↑) • (Swap ↑ • CS • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • CK₁₀ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b3 : Chain (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ Sw01 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ Sw01 ∷ [])
  b3 = at 25 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 24 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 23 2 (Sw01 ∷ X1 ∷ []) (win 3 0 complete₃ (X • Swap) (Swap • (X ↑)) tt tt Eq.refl) ▸
       at 22 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 21 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸
       at 20 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 19 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 18 2 (Sw01 ∷ CK21 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CK₁₀ • Swap ↑) • Swap) (Swap • (CK₁₀ ↑)) tt tt Eq.refl) ▸ done

  b4 : Chain (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ Sw01 ∷ CK21 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ Sw01 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ [])
  b4 = at 17 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 16 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 15 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 14 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 15 11 (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CS • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • (X ↑) • CK₁₀ • (X ↑) • X • (X ↑ ↑)) (X • (X ↑ ↑) • (X ↑) • (CS • CS • CS) • (X ↑)) tt tt Eq.refl) ▸
       at 14 2 (X0 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (X ↑)) (X • Swap) tt tt Eq.refl) ▸
       at 15 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 16 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b5 : Chain (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b5 = at 17 2 (CS02⁻ ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • ((CS • CS • CS) ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 18 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 19 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CSd20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CSd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (CS02⁻ ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = run b0
  where
  b0 : Chain (CS02⁻ ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ [])
  b0 = at 1 2 (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑))) ▸
       at 0 2 (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 19 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 19 (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3) ▸
       at 17 4 (X2 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (X0 ∷ X2 ∷ []) (sym (low₁-comm (X) ((X ↑)))) ▸
       at 16 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

