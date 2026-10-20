{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D374 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00257 ; wn00258 ; wn00389 ; wn00390)
open import Examples.Groups.Clifford+CS.Four.Wins.W20 using (wn01018 ; wn01019 ; wn01020 ; wn01021 ; wn01022 ; wn01023 ; wn01024 ; wn01025 ; wn01026 ; wn01027 ; wn01028 ; wn01029 ; wn01030)

-- distribute Gad(t=1, W=(2, 3), d=1, e=-1) CS13 TOFF102 CSd13 TOFF102: 15 steps
lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = trans (run b0) (run b1)
  where
  b0 : Chain (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ X3 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  b0 = at 3 0 (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) wn01018 ▸
       at 8 0 (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) wn01018 ▸
       at 13 0 (X2 ∷ X3 ∷ X2 ∷ X3 ∷ []) wn01018 ▸
       at 0 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 2 2 [] wn00389 ▸
       at 4 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 5 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

  b1 : Chain (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ X3 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ X3 ∷ Toff102 ∷ X2 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b1 = at 6 2 [] wn00390 ▸
       at 6 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 7 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 8 2 [] wn00389 ▸
       at 10 2 (Toff102 ∷ X3 ∷ []) (sym (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))) ▸
       at 11 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 12 2 [] wn00390 ▸ done

-- pass [X2 CS23 X2] [CS01]: 3 steps
lem-pass-X2-CS23-X2-vs-CS01 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-CS01 = run b0
  where
  b0 : Chain (X2 ∷ CS23 ∷ X2 ∷ CS01 ∷ []) (CS01 ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸
       at 1 2 (CS01 ∷ CS23 ∷ []) (sym (low-comm (CS) (CS))) ▸
       at 0 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸ done

-- pass [X2 CS23 X2] [TOFF123]: 1 steps
lem-pass-X2-CS23-X2-vs-TOFF123 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-TOFF123 = run b0
  where
  b0 : Chain (X2 ∷ CS23 ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff123 ∷ X2 ∷ CS23 ∷ X2 ∷ []) wn01019 ▸ done

-- pass [X2 CS23 X2] [CSd01]: 3 steps
lem-pass-X2-CS23-X2-vs-CSd01 : ⟪ (X2 ∷ CS23 ∷ X2 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS23-X2-vs-CSd01 = run b0
  where
  b0 : Chain (X2 ∷ CS23 ∷ X2 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X2 ∷ CS23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸
       at 1 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 0 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸ done

-- pass [X2 CK23 X2] [CS01]: 3 steps
lem-pass-X2-CK23-X2-vs-CS01 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-CS01 = run b0
  where
  b0 : Chain (X2 ∷ CK23 ∷ X2 ∷ CS01 ∷ []) (CS01 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸
       at 1 2 (CS01 ∷ CK23 ∷ []) (sym (low-comm (CS) (CK₀₁))) ▸
       at 0 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸ done

-- pass [X2 CK23 X2] [TOFF123]: 1 steps
lem-pass-X2-CK23-X2-vs-TOFF123 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-TOFF123 = run b0
  where
  b0 : Chain (X2 ∷ CK23 ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  b0 = at 0 4 (Toff123 ∷ X2 ∷ CK23 ∷ X2 ∷ []) wn01020 ▸ done

-- pass [X2 CK23 X2] [CSd01]: 3 steps
lem-pass-X2-CK23-X2-vs-CSd01 : ⟪ (X2 ∷ CK23 ∷ X2 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK23-X2-vs-CSd01 = run b0
  where
  b0 : Chain (X2 ∷ CK23 ∷ X2 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X2 ∷ CK23 ∷ X2 ∷ [])
  b0 = at 2 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸
       at 1 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸
       at 0 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸ done

-- pass [X2 CSd23 X2] [CS01]: 3 steps
lem-pass-X2-CSd23-X2-vs-CS01 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS01 = run b0
  where
  b0 : Chain (X2 ∷ CS23⁻ ∷ X2 ∷ CS01 ∷ []) (CS01 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  b0 = at 2 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸
       at 1 2 (CS01 ∷ CS23⁻ ∷ []) (sym (low-comm (CS) ((CS • CS • CS)))) ▸
       at 0 2 (CS01 ∷ X2 ∷ []) (sym (low-comm (CS) (X))) ▸ done

-- pass [X2 CSd23 X2] [TOFF123]: 1 steps
lem-pass-X2-CSd23-X2-vs-TOFF123 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-TOFF123 = run b0
  where
  b0 : Chain (X2 ∷ CS23⁻ ∷ X2 ∷ Toff123 ∷ []) (Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (Toff123 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) wn01021 ▸ done

-- pass [X2 CSd23 X2] [CSd01]: 3 steps
lem-pass-X2-CSd23-X2-vs-CSd01 : ⟪ (X2 ∷ CS23⁻ ∷ X2 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CSd01 = run b0
  where
  b0 : Chain (X2 ∷ CS23⁻ ∷ X2 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X2 ∷ CS23⁻ ∷ X2 ∷ [])
  b0 = at 2 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸
       at 1 2 (CS01⁻ ∷ CS23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((CS • CS • CS)))) ▸
       at 0 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸ done

-- pass [CCZ123] [X2 CS12 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CS12-X2 : ⟪ (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CS12-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CS12 ∷ X2 ∷ CCZ123 ∷ []) wn01022 ▸ done

-- pass [CCZ123] [X2 CK21 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CK21-X2 : ⟪ (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CK21-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CK21 ∷ X2 ∷ CCZ123 ∷ []) wn01023 ▸ done

-- pass [CZ13] [CS13]: 1 steps
lem-pass-CZ13-vs-CS13 : ⟪ (CZ13 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CZ13 ∷ []) ⟫ʷ
lem-pass-CZ13-vs-CS13 = run b0
  where
  b0 : Chain (CZ13 ∷ CS13 ∷ []) (CS13 ∷ CZ13 ∷ [])
  b0 = at 0 2 (CS13 ∷ CZ13 ∷ []) wn01024 ▸ done

-- pass [Z1] [CS13]: 1 steps
lem-pass-Z1-vs-CS13 : ⟪ (Z1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Z1 ∷ []) ⟫ʷ
lem-pass-Z1-vs-CS13 = run b0
  where
  b0 : Chain (Z1 ∷ CS13 ∷ []) (CS13 ∷ Z1 ∷ [])
  b0 = at 0 2 (CS13 ∷ Z1 ∷ []) wn01025 ▸ done

-- pass [CZ13] [CSd13]: 1 steps
lem-pass-CZ13-vs-CSd13 : ⟪ (CZ13 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CZ13 ∷ []) ⟫ʷ
lem-pass-CZ13-vs-CSd13 = run b0
  where
  b0 : Chain (CZ13 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ13 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ CZ13 ∷ []) wn01026 ▸ done

-- pass [Z1] [CSd13]: 1 steps
lem-pass-Z1-vs-CSd13 : ⟪ (Z1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Z1 ∷ []) ⟫ʷ
lem-pass-Z1-vs-CSd13 = run b0
  where
  b0 : Chain (Z1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Z1 ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ Z1 ∷ []) wn01027 ▸ done

-- pass [CCZ123] [X2 CKd21 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CKd21-X2 : ⟪ (CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CKd21-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CK21⁻ ∷ X2 ∷ CCZ123 ∷ []) wn01028 ▸ done

-- pass [CCZ123] [X2 CSd12 X2]: 1 steps
lem-pass-CCZ123-vs-X2-CSd12-X2 : ⟪ (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X2-CSd12-X2 = run b0
  where
  b0 : Chain (CCZ123 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ [])
  b0 = at 0 4 (X2 ∷ CS12⁻ ∷ X2 ∷ CCZ123 ∷ []) wn01029 ▸ done

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
  b0 = at 0 4 (Toff123 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) wn01030 ▸ done

-- pass [X2 CKd23 X2] [CSd01]: 3 steps
lem-pass-X2-CKd23-X2-vs-CSd01 : ⟪ (X2 ∷ CK23⁻ ∷ X2 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CSd01 = run b0
  where
  b0 : Chain (X2 ∷ CK23⁻ ∷ X2 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X2 ∷ CK23⁻ ∷ X2 ∷ [])
  b0 = at 2 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸
       at 1 2 (CS01⁻ ∷ CK23⁻ ∷ []) (sym (low-comm ((CS • CS • CS)) ((S • CK₀₁)))) ▸
       at 0 2 (CS01⁻ ∷ X2 ∷ []) (sym (low-comm ((CS • CS • CS)) (X))) ▸ done
