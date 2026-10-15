{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D611 where

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
open import Examples.Groups.Clifford+CS.Four.D.D001 using (lem-T-CZ03-T)
open import Examples.Groups.Clifford+CS.Four.D.D164 using (lem-S2-at1203-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D610 using (lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CSd23-X2-vs-CS01 ; lem-pass-X2-CSd23-X2-vs-TOFF123)
-- pass [X2 CSd23 X2] [CSd01]: 3 steps
lem-pass-X2-CSd23-X2-vs-CSd01 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CSd01 = run b0
  where
  b0 : Chain (X2 ∷ CS23⁻ ∷ X2 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  b0 = at 2 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸
       at 1 2 (CS01⁻ ∷ CS23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((CS • CS • CS)))) ▸
       at 0 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸ done


-- pass [X2 CSd23 X2] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = run b0
  where
  b0 : Chain (X2 ∷ CS23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS01 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CS01) ▸
       at 1 4 (Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF123) ▸
       at 2 4 (CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CSd01) ▸
       at 3 4 (Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-TOFF123) ▸ done


-- pass [X2 CSd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CS23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done


-- pass [X2 CKd23 X2] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 9 steps
lem-pass-X2-CKd23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 17 (S1 ∷ K1 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • S • K) (S • K • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 15 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 12 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 9 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 6 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 3 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 7 17 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23 ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b1 = at 9 16 (X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CS ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CKd23] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (CK23⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK23⁻ ∷ []) ⟫ʷ
lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = run b0
  where
  b0 : Chain (CK23⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK23⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ (((S • CK₀₁) ↑) • (X ↑)) ((X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 13 (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3) ▸
       at 11 4 (X2 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑)) ((X ↑) • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [CCZ123] [X2 CS12 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CS12-X2 : ⟪ (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CS12-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (X ↑) • CS • (X ↑)) ((X ↑) • CS • (X ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X2 CK21 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CK21-X2 : ⟪ (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CK21-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (X ↑) • CK₁₀ • (X ↑)) ((X ↑) • CK₁₀ • (X ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CZ13] [CS13]: 1 steps
lem-pass-CZ13-vs-CS13 : ⟪ (CZ13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CZ13 ∷ []) ⟫ʷ
lem-pass-CZ13-vs-CS13 = run b0
  where
  b0 : Chain (CZ13 ∷ CS13 ∷ []) (CS13 ∷ CZ13 ∷ [])
  b0 = at 0 2 (CS13 ∷ CZ13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [Z1] [CS13]: 1 steps
lem-pass-Z1-vs-CS13 : ⟪ (Z1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Z1 ∷ []) ⟫ʷ
lem-pass-Z1-vs-CS13 = run b0
  where
  b0 : Chain (Z1 ∷ CS13 ∷ []) (CS13 ∷ Z1 ∷ [])
  b0 = at 0 2 (CS13 ∷ Z1 ∷ []) (win 0 3 complete₃ (Z • (Swap ↑ • CS • Swap ↑)) ((Swap ↑ • CS • Swap ↑) • Z) tt tt Eq.refl) ▸ done


-- T-CZ03-T @1023: 58 steps
lem-T-CZ03-T-at1023 : ⟪ (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ13 ∷ []) ⟫ʷ
lem-T-CZ03-T-at1023 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) (Toff102 ∷ CZ13 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ [])
  b0 = at 3 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 8 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 7 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff102 ∷ CZ13 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ []) (Toff102 ∷ Sw01 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ [])
  b1 = at 3 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 3 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CZ02 ∷ []) (win 3 0 complete₃ ((CZ ↑) • Swap) (Swap • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (Toff102 ∷ Sw01 ∷ Sw23 ∷ CZ02 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ []) (K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CZ03 ∷ Toff012 ∷ Sw01 ∷ [])
  b2 = at 2 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ ι1 ∷ []) (win 3 0 complete₃ (iI • Swap) (Swap • (iI ↑)) tt tt Eq.refl) ▸
       at 6 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) (win 3 0 complete₃ ((Swap ↑ • CS • Swap ↑) • Swap) (Swap • (CS ↑)) tt tt Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸
       at 3 2 (Sw01 ∷ CS02⁻ ∷ []) (win 3 0 complete₃ (((CS • CS • CS) ↑) • Swap) (Swap • (Swap ↑ • (CS • CS • CS) • Swap ↑)) tt tt Eq.refl) ▸
       at 2 2 (Sw01 ∷ CX10 ∷ []) (win 3 0 complete₃ (CX₀₁ • Swap) (Swap • CX₁₀) tt tt Eq.refl) ▸ done

  b3 : Chain (K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CZ03 ∷ Toff012 ∷ Sw01 ∷ []) (CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ03 ∷ Sw01 ∷ [])
  b3 = at 1 2 (Sw01 ∷ CS02 ∷ []) (win 3 0 complete₃ ((CS ↑) • Swap) (Swap • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 0 2 (Sw01 ∷ K0 ∷ []) (win 3 0 complete₃ ((K ↑) • Swap) (Swap • K) tt tt Eq.refl) ▸
       at 1 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (win 3 0 complete₃ (K • (Swap ↑ • CS • Swap ↑) • CX₁₀ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • CX₁₀ • (CS ↑) • K • (iI ↑)) (K • (CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑) • K • iI) tt tt Eq.refl) ▸
       at 1 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ123 ∷ CZ03 ∷ []) (lem-T-CZ03-T) ▸
       at 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 1 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸ done

  b4 : Chain (CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CZ03 ∷ Sw01 ∷ [])
  b4 = at 2 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 3 2 (CX02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CX₀₁ ↑)) ((Swap ↑ • CX₀₁ • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (CS ↑)) ((Swap ↑ • CS • Swap ↑) • Swap) tt tt Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw01 ∷ Sw01 ∷ []) (win 3 0 complete₃ (ε) (Swap • Swap) tt tt Eq.refl) ▸ done

  b5 : Chain (Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CZ03 ∷ Sw01 ∷ [])
  b5 = at 1 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 2 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 4 2 (CX12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CX₀₁ • Swap ↑)) ((CX₀₁ ↑) • Swap) tt tt Eq.refl) ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CS12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • Swap) tt tt Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b6 : Chain (Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CZ03 ∷ Sw01 ∷ []) (CCZ023 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ [])
  b6 = at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (win 0 3 complete₃ ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) ((CS ↑) • CX₀₁ • ((CS • CS • CS) ↑) • CX₀₁ • (Swap ↑ • CS • Swap ↑)) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 0 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CZ12 ∷ Sw01 ∷ []) (win 3 0 complete₃ (Swap • (Swap ↑ • CZ • Swap ↑)) ((CZ ↑) • Swap) tt tt Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b7 : Chain (CCZ023 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ []) (CCZ023 ∷ CZ13 ∷ [])
  b7 = at 1 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (win 3 0 complete₃ (Swap • Swap) (ε) tt tt Eq.refl) ▸ done


-- pass [CZ13] [CSd13]: 1 steps
lem-pass-CZ13-vs-CSd13 : ⟪ (CZ13 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CZ13 ∷ []) ⟫ʷ
lem-pass-CZ13-vs-CSd13 = run b0
  where
  b0 : Chain (CZ13 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ13 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CZ13 ∷ []) (win 0 3 complete₃ ((Swap ↑ • CZ • Swap ↑) • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • (Swap ↑ • CZ • Swap ↑)) tt tt Eq.refl) ▸ done


-- pass [Z1] [CSd13]: 1 steps
lem-pass-Z1-vs-CSd13 : ⟪ (Z1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Z1 ∷ []) ⟫ʷ
lem-pass-Z1-vs-CSd13 = run b0
  where
  b0 : Chain (Z1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Z1 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ Z1 ∷ []) (win 0 3 complete₃ (Z • (Swap ↑ • (CS • CS • CS) • Swap ↑)) ((Swap ↑ • (CS • CS • CS) • Swap ↑) • Z) tt tt Eq.refl) ▸ done

