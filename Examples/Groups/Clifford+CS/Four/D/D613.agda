{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D613 where

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
open import Examples.Groups.Clifford+CS.Four.D.D163 using (lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2)
open import Examples.Groups.Clifford+CS.Four.D.D164 using (lem-S2-at1203-ᵖ-1)
open import Examples.Groups.Clifford+CS.Four.D.D610 using (lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D611 using (lem-pass-CCZ123-vs-X2-CK21-X2 ; lem-pass-CCZ123-vs-X2-CS12-X2 ; lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 ; lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D612 using (lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102)
-- pass [CS13 TOFF102 CSd13 TOFF102] [Z1 CZ12 CZ13 CCZ123]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 = run b0
  where
  b0 : Chain (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  b0 = at 0 8 (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102) ▸ done


-- pass [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 : ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (X2 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b0 = at 7 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 6 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 8 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 2 8 (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123) ▸
       at 1 2 (Z1 ∷ X3 ∷ []) (sym (low-comm ((Z ↑)) ((X ↑)))) ▸
       at 2 2 (CZ12 ∷ X3 ∷ []) (sym (low₃-comm ((CZ ↑)) (X))) ▸
       at 3 2 (Z1 ∷ CZ13 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • (Swap ↑ • CZ • Swap ↑)) (Z • (Swap ↑ • CZ • Swap ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 5 2 (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (win 0 3 complete₃ ((X ↑ ↑) • CCZ) (CZ • CCZ • (X ↑ ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X2 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ CZ12 ∷ CCZ123 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (CCZ123 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b1 = at 0 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 1 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 3 2 (Z1 ∷ X2 ∷ []) (sym (low-comm ((Z ↑)) (X))) ▸
       at 4 2 (CZ13 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (Swap ↑ • CZ • Swap ↑)) ((Swap ↑ • CZ • Swap ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 5 2 (Z1 ∷ CZ12 ∷ X2 ∷ []) (win 3 0 complete₃ ((X ↑ ↑) • (CZ ↑)) ((Z ↑) • (CZ ↑) • (X ↑ ↑)) tt tt Eq.refl) ▸
       at 7 2 (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • CCZ) ((Swap ↑ • CZ • Swap ↑) • CCZ • (X ↑)) tt tt Eq.refl) ▸
       at 0 9 (CCZ123 ∷ []) (win 0 3 complete₃ (Z • Z • CZ • Z • (Swap ↑ • CZ • Swap ↑) • Z • CZ • (Swap ↑ • CZ • Swap ↑) • CCZ) (CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 1 steps
lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 0 9 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (sym lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123) ▸ done


-- pass [CCZ123] [X2 CKd21 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CKd21-X2 : ⟪ (CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CKd21-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (X ↑) • (S ↑ • CK₁₀) • (X ↑)) ((X ↑) • (S ↑ • CK₁₀) • (X ↑) • CCZ) tt tt Eq.refl) ▸ done


-- pass [CCZ123] [X2 CSd12 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CSd12-X2 : ⟪ (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CSd12-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (win 0 3 complete₃ (CCZ • (X ↑) • (CS • CS • CS) • (X ↑)) ((X ↑) • (CS • CS • CS) • (X ↑) • CCZ) tt tt Eq.refl) ▸ done


-- CCZ(2,1,3) passes split Gad(t=1, W=(2, 3), d=SK, e=-1): 5 steps
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : ⟪ (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CS12-X2) ▸
       at 3 4 (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CK21-X2) ▸
       at 6 9 (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3) ▸
       at 14 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CKd21-X2) ▸
       at 17 4 (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-CSd12-X2) ▸ done


-- pass [CCZ123] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 3 steps
lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (CCZ123 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ [])
  b0 = at 1 12 (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2) ▸
       at 0 21 (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) (lem-CCZ⟨213⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩) ▸
       at 0 20 (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (sym lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2) ▸ done


-- pass [X2 CKd23 X2] [CS01]: 3 steps
lem-pass-X2-CKd23-X2-vs-CS01 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS01 = run b0
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ CS01 ∷ []) (CS01 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b0 = at 2 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸
       at 1 2 (CS01 ∷ CK23⁻ ∷ []) (sym (low-comm (CS) ((S • CK₀₁)))) ▸
       at 0 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸ done


-- pass [X2 CKd23 X2] [TOFF123]: 1 steps
lem-pass-X2-CKd23-X2-vs-TOFF123 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-TOFF123 = run b0
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((S • CK₀₁) ↑) • (X ↑) • Toff) (Toff • (X ↑) • ((S • CK₀₁) ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [X2 CKd23 X2] [CSd01]: 3 steps
lem-pass-X2-CKd23-X2-vs-CSd01 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CSd01 = run b0
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b0 = at 2 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸
       at 1 2 (CS01⁻ ∷ CK23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((S • CK₀₁)))) ▸
       at 0 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸ done


-- pass [X2 CKd23 X2] [CS01 TOFF123 CSd01 TOFF123]: 4 steps
lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = run b0
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (CS01 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-CS01) ▸
       at 1 4 (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-TOFF123) ▸
       at 2 4 (CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-CSd01) ▸
       at 3 4 (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-TOFF123) ▸ done


-- pass [X2 CKd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = run b0
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b0 = at 3 4 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ []) (lem-S2-at1203-ᵖ-1) ▸
       at 0 7 (CS01 ∷ Toff123 ∷ CS01⁻ ∷ Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123) ▸
       at 0 4 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (sym lem-S2-at1203-ᵖ-1) ▸ done


-- pass [X2 CK23 X2] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 9 steps
lem-pass-X2-CK23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ CK23 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X3 ∷ [])
  b0 = at 0 4 (X3 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 1 17 (S1 ∷ K1 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • S • K) (S • K • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 15 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 12 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 9 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23 ∷ X2 ∷ []) (lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 6 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 3 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 7 17 (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (K • iI) • (S • S • S)) ((K • iI) • (S • S • S) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑)) tt tt Eq.refl) ▸ done

  b1 : Chain (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23 ∷ X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  b1 = at 9 16 (X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (win 0 3 complete₃ ((X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • (CS ↑) • (X ↑) • (X ↑) • ((S • CK₀₁) ↑) • (X ↑) • (X ↑) • ((CS • CS • CS) ↑) • (X ↑) • (X ↑ ↑)) ((X ↑ ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) tt tt Eq.refl) ▸ done


-- pass [CK23] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (CK23 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = run b0
  where
  b0 : Chain (CK23 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK23 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • (X ↑)) ((X ↑) • (X ↑) • (CK₀₁ ↑) • (X ↑)) tt tt Eq.refl) ▸
       at 13 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 13 (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3) ▸
       at 11 4 (X2 ∷ CK23 ∷ []) (win 0 3 complete₃ ((X ↑) • (CK₀₁ ↑) • (X ↑) • (X ↑)) ((X ↑) • (CK₀₁ ↑)) tt tt Eq.refl) ▸
       at 10 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done


-- pass [TOFF312] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (Toff312 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = run b0
  where
  b0 : Chain (Toff312 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ Toff312 ∷ [])
  b0 = at 0 1 (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) (win 0 3 complete₃ (Toffᵗ) ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) tt tt Eq.refl) ▸
       at 2 13 (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK23⁻ ∷ []) (lem-pass-CKd23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3) ▸
       at 1 13 (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3) ▸
       at 0 13 (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK23 ∷ []) (lem-pass-CK23-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3) ▸
       at 12 3 (Toff312 ∷ []) (win 0 3 complete₃ ((CK₀₁ ↑) • CCZ • ((S • CK₀₁) ↑)) (Toffᵗ) tt tt Eq.refl) ▸ done

