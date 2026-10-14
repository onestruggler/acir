{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D089 where

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
open import Examples.Groups.Clifford+CS.Four.D.D025 using (lem-pass-CS13-vs-CS02)
open import Examples.Groups.Clifford+CS.Four.D.D029 using (lem-pass-CSd02-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D030 using (lem-pass-CCZ012-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D072 using (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D073 using (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 ; lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D084 using (lem-pass-CCZ012-vs-CZ02)
open import Examples.Groups.Clifford+CS.Four.D.D086 using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D087 using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D088 using (lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 ; lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 ; lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
-- pass [X2 CK21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = run b0
  where
  b0 : Chain (X2 ∷ CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  b0 = at 0 5 (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 14 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 11 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 8 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 17 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [CK21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = run b0
  where
  b0 : Chain (CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (win 3 0 complete₃ ((CK₁₀ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 11 (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1) ▸
       at 9 4 (X2 ∷ CK21 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CK₁₀ ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CK₁₀ ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CS21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 5 (S1 ∷ K1 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (S ↑) • (K ↑)) ((S ↑) • (K ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 5 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 2 7 (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13) ▸
       at 6 11 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((S ↑ • CK₁₀) ↑) • (X ↑ ↑) • (X ↑ ↑) • ((CS • CS • CS) ↑) • (X ↑ ↑) • ((K • iI) ↑) • ((S • S • S) ↑)) (((K • iI) ↑) • ((S • S • S) ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸ done


-- pass [CS21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = run b0
  where
  b0 : Chain (CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (win 3 0 complete₃ ((CS ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑ ↑) • (CS ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 1 11 (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1) ▸
       at 9 4 (X2 ∷ CS12 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CS ↑) • (X ↑ ↑) • (X ↑ ↑)) ((X ↑ ↑) • (CS ↑)) tt tt Eq.refl) ▸ done


-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = run b0
  where
  b0 : Chain (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ [])
  b0 = at 0 8 (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2) ▸
       at 7 11 (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ []) (lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2) ▸
       at 6 11 (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ []) (lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2) ▸
       at 2 14 (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2) ▸
       at 1 11 (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ []) (lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2) ▸
       at 0 11 (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2) ▸
       at 10 8 (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2) ▸ done


-- pass [S1] [CS13]: 1 steps
lem-pass-S1-vs-CS13 : ⟪ (S1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-CS13 = run b0
  where
  b0 : Chain (S1 ∷ CS13 ∷ []) (CS13 ∷ S1 ∷ [])
  b0 = at 0 2 (CS13 ∷ S1 ∷ []) (win 0 3 complete₃ (S • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • S) tt tt Eq.refl) ▸ done


-- pass [CCZ012] [CS02]: 1 steps
lem-pass-CCZ012-vs-CS02 : ⟪ (CCZ012 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS02 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS02 ∷ []) (CS02 ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [S1] [CSd13]: 1 steps
lem-pass-S1-vs-CSd13 : ⟪ (S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-CSd13 = run b0
  where
  b0 : Chain (S1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S1 ∷ []) (win 0 3 complete₃ (S • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • S) tt tt Eq.refl) ▸ done


-- pass [S1] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13 = trans (run b0) (run b1)
  where
  b0 : Chain (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ S1 ∷ CS02 ∷ CS02 ∷ CCZ012 ∷ CZ02 ∷ CCZ012 ∷ CS13⁻ ∷ [])
  b0 = at 0 2 (Toff102 ∷ S1 ∷ CS02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((S ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (S ↑) • (Swap ↑ • CS • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS13 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS13) ▸
       at 2 2 (CS13 ∷ CS02 ∷ []) (sym lem-pass-CS13-vs-CS02) ▸
       at 1 2 (CS13 ∷ S1 ∷ []) (lem-pass-S1-vs-CS13) ▸
       at 4 2 (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ CS02 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ S1 ∷ CS02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ ((S ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (S ↑) • (Swap ↑ • CS • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 5 2 (CS02 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS02) ▸ done

  b1 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ S1 ∷ CS02 ∷ CS02 ∷ CCZ012 ∷ CZ02 ∷ CCZ012 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ [])
  b1 = at 6 2 (CZ02 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ02) ▸
       at 4 3 [] (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ S1 ∷ []) (lem-pass-S1-vs-CSd13) ▸ done


-- pass [TOFF102 CS13 TOFF102 CSd13] [S1]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ []) (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 5 (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13) ▸ done


-- pass [Sd1] [CS13]: 1 steps
lem-pass-Sd1-vs-CS13 : ⟪ (S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-CS13 = run b0
  where
  b0 : Chain (S1⁻ ∷ CS13 ∷ []) (CS13 ∷ S1⁻ ∷ [])
  b0 = at 0 2 (CS13 ∷ S1⁻ ∷ []) (win 0 3 complete₃ ((S • S • S) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (S • S • S)) tt tt Eq.refl) ▸ done


-- pass [CCZ012] [CSd02]: 1 steps
lem-pass-CCZ012-vs-CSd02 : ⟪ (CCZ012 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd02 = run b0
  where
  b0 : Chain (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [Sd1] [CSd13]: 1 steps
lem-pass-Sd1-vs-CSd13 : ⟪ (S1⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-CSd13 = run b0
  where
  b0 : Chain (S1⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S1⁻ ∷ []) (win 0 3 complete₃ ((S • S • S) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (S • S • S)) tt tt Eq.refl) ▸ done


-- pass [Sd1] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 = trans (run b0) (run b1)
  where
  b0 : Chain (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ S1⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CCZ012 ∷ CZ02 ∷ CCZ012 ∷ CS13⁻ ∷ [])
  b0 = at 0 2 (Toff102 ∷ S1⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (CS13 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS13) ▸
       at 2 2 (CS13 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CS13) ▸
       at 1 2 (CS13 ∷ S1⁻ ∷ []) (lem-pass-Sd1-vs-CS13) ▸
       at 4 2 (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) (win 3 0 complete₃ (CCZ • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • CZ • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 3 2 (Toff102 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Toff102 ∷ S1⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) (win 3 0 complete₃ (((S • S • S) ↑) • (K ↑ • CCZ • K ↑ • iI)) ((K ↑ • CCZ • K ↑ • iI) • ((S • S • S) ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CCZ) tt tt Eq.refl) ▸
       at 5 2 (CS02⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd02) ▸ done

  b1 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ S1⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CCZ012 ∷ CZ02 ∷ CCZ012 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ [])
  b1 = at 6 2 (CZ02 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ02) ▸
       at 4 3 [] (win 3 0 complete₃ ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) (ε) tt tt Eq.refl) ▸
       at 4 2 [] (win 3 0 complete₃ (CCZ • CCZ) (ε) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ S1⁻ ∷ []) (lem-pass-Sd1-vs-CSd13) ▸ done


-- pass [TOFF102 CS13 TOFF102 CSd13] [Sd1]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 5 (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (sym lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13) ▸ done


-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 7 (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2) ▸
       at 3 5 (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1) ▸
       at 4 5 (CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13) ▸
       at 5 7 (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2) ▸
       at 8 5 (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1) ▸
       at 9 5 (CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13) ▸ done

