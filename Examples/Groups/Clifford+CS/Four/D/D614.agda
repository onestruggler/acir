{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D614 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00031 ; wn00116 ; wn00137 ; wn00139 ; wn00173 ; wn00175)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01359 ; wn01360 ; wn01361 ; wn01407 ; wn01408)
open import Examples.Groups.Clifford+CS.Four.Wins.W28 using (wn01485 ; wn01494 ; wn01500)
open import Examples.Groups.Clifford+CS.Four.Wins.W34 using (wn01670 ; wn01672 ; wn01673 ; wn01677 ; wn01678 ; wn01680)
open import Examples.Groups.Clifford+CS.Four.Wins.W35 using (wn01689 ; wn01709 ; wn01710 ; wn01711 ; wn01712 ; wn01713 ; wn01748 ; wn01749)
open import Examples.Groups.Clifford+CS.Four.Wins.W37 using (wn01833 ; wn01834)
open import Examples.Groups.Clifford+CS.Four.D.D009 using (lem-pass-CS13-vs-CS03 ; lem-pass-CS13-vs-CSd03 ; lem-pass-CSd13-vs-CS03 ; lem-pass-CSd13-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D011 using (lem-pass-CS03-vs-S1 ; lem-pass-CS03-vs-Sd1)
open import Examples.Groups.Clifford+CS.Four.D.D015 using (lem-pass-CSd03-vs-S1 ; lem-pass-CSd03-vs-Sd1 ; lem-pass-TOFF012-vs-S1 ; lem-pass-TOFF012-vs-Sd1 ; lem-pass-TOFF012-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D538 using (lem-pass-TOFF012-vs-CS13 ; lem-pass-TOFF012-vs-CSd13 ; lem-pass-TOFF102-vs-CS03 ; lem-pass-TOFF102-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D541 using (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D542 using (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D544 using (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D590 using (lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [TOFF012] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 4 steps
lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = run b0
  where
  b0 : Chain (Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ [])
  b0 = at 0 2 (CS13 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CS13) ▸
       at 1 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸
       at 4 2 (CS13⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CSd13) ▸
       at 5 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸ done

-- pass [CSd03] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 26 steps
lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (CS03⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b0 = at 0 2 (CS13 ∷ CS03⁻ ∷ []) (sym lem-pass-CS13-vs-CSd03) ▸
       at 2 3 (CX01 ∷ Toff102 ∷ []) wn01359 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (CX01 ∷ CS02⁻ ∷ []) wn01748 ▸
       at 1 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b1 : Chain (CS13 ∷ CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 1 2 (X2 ∷ Toff102 ∷ X2 ∷ []) wn01361 ▸
       at 4 2 (CS13⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-CSd13-vs-CSd03) ▸
       at 6 3 (CX01 ∷ Toff102 ∷ []) wn01359 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CS03⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CX01 ∷ CS03⁻ ∷ Toff102 ∷ [])
  b2 = at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 6 2 (CX01 ∷ CS02⁻ ∷ []) wn01748 ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b3 : Chain (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ CX01 ∷ CS03⁻ ∷ Toff102 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ [])
  b3 = at 6 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 5 2 (X2 ∷ Toff102 ∷ X2 ∷ []) wn01361 ▸ done

-- pass [CS03] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 28 steps
lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (CS03 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b0 = at 0 2 (S1 ∷ CS03 ∷ []) (lem-pass-CS03-vs-S1) ▸
       at 1 2 (CS13⁻ ∷ CS03 ∷ []) (sym lem-pass-CSd13-vs-CS03) ▸
       at 3 3 (CX01 ∷ Toff102 ∷ []) wn01359 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ CS02 ∷ []) wn01360 ▸ done

  b1 : Chain (S1 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CS03 ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b1 = at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 2 (Toff102 ∷ CS03 ∷ []) (sym lem-pass-TOFF102-vs-CS03) ▸
       at 2 2 (X2 ∷ Toff102 ∷ X2 ∷ []) wn01361 ▸
       at 5 2 (S1⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-Sd1) ▸
       at 6 2 (CS13 ∷ CS03 ∷ []) (sym lem-pass-CS13-vs-CS03) ▸ done

  b2 : Chain (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CS03 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ [])
  b2 = at 8 3 (CX01 ∷ Toff102 ∷ []) wn01359 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ CS02 ∷ []) wn01360 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b3 : Chain (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ [])
  b3 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 8 2 (Toff102 ∷ CS03 ∷ []) (sym lem-pass-TOFF102-vs-CS03) ▸
       at 7 2 (X2 ∷ Toff102 ∷ X2 ∷ []) wn01361 ▸ done

-- pass [TOFF012] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 6 steps
lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = run b0
  where
  b0 : Chain (Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ [])
  b0 = at 0 2 (S1 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-S1) ▸
       at 1 2 (CS13⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CSd13) ▸
       at 2 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸
       at 5 2 (S1⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Sd1) ▸
       at 6 2 (CS13 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CS13) ▸
       at 7 4 (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2) ▸ done

-- pass [CSd03] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 28 steps
lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (CS03⁻ ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03⁻ ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02⁻ ∷ Sw23 ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b0 = at 0 2 (S1 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-S1) ▸
       at 1 2 (CS13⁻ ∷ CS03⁻ ∷ []) (sym lem-pass-CSd13-vs-CSd03) ▸
       at 3 3 (CX01 ∷ Toff102 ∷ []) wn01359 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 2 (CX01 ∷ CS02⁻ ∷ []) wn01748 ▸ done

  b1 : Chain (S1 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02⁻ ∷ Sw23 ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CS03⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ [])
  b1 = at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 3 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 2 2 (X2 ∷ Toff102 ∷ X2 ∷ []) wn01361 ▸
       at 5 2 (S1⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Sd1) ▸
       at 6 2 (CS13 ∷ CS03⁻ ∷ []) (sym lem-pass-CS13-vs-CSd03) ▸ done

  b2 : Chain (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CS03⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ [])
  b2 = at 8 3 (CX01 ∷ Toff102 ∷ []) wn01359 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 8 2 (CX01 ∷ CS02⁻ ∷ []) wn01748 ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b3 : Chain (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff102 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ [])
  b3 = at 8 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 8 2 (Toff102 ∷ CS03⁻ ∷ []) (sym lem-pass-TOFF102-vs-CSd03) ▸
       at 7 2 (X2 ∷ Toff102 ∷ X2 ∷ []) wn01361 ▸ done

-- CA CKd30 Gad(t=0, W=(2,), d=1, e=-1): 25 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : ⟪ (CK30⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK30⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (K0⁻ ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 1 (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn01709 ▸
       at 0 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (K0⁻ ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 [] wn00003 ▸
       at 1 9 (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2) ▸
       at 0 2 (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑))) ▸
       at 1 1 (K0⁻ ∷ []) wn01710 ▸
       at 6 0 (K0 ∷ K0⁻ ∷ []) wn00116 ▸
       at 7 2 (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b2 : Chain (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ Sw23 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ CK30⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 8 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 9 4 (CK20⁻ ∷ []) wn01711 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ CK30⁻ ∷ Sw23 ∷ Sw23 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ CK30⁻ ∷ [])
  b3 = at 9 2 [] wn00003 ▸ done

-- pass [X3 CKd30 X3] [X2 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2]: 65 steps
lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ Sw01 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ Sw01 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ [])
  b1 = at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) wn01677 ▸
       at 0 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b2 : Chain (X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ [])
  b2 = at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

  b3 : Chain (X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ [])
  b3 = at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 4 (K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01712 ▸
       at 1 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 2 [] wn00003 ▸ done

  b4 : Chain (X2 ∷ K0⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ [])
  b4 = at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 7 4 (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01713 ▸ done

  b5 : Chain (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ [])
  b5 = at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 2 [] wn00003 ▸
       at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸ done

  b6 : Chain (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ Sw01 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 9 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 8 4 (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) wn01677 ▸ done

  b7 : Chain (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ Sw01 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ Sw01 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw01 ∷ Sw01 ∷ [])
  b7 = at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 8 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b8 : Chain (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw01 ∷ Sw01 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b8 = at 11 2 [] wn00031 ▸ done

-- pass [X1 CS10 X1] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 5 steps
lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = run b0
  where
  b0 : Chain (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) wn01680 ▸
       at 1 3 (X1 ∷ CS01 ∷ X1 ∷ []) wn01670 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 5 3 (X1 ∷ CS01 ∷ X1 ∷ []) wn01670 ▸
       at 5 4 (X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) wn01680 ▸ done

-- pass [X1 CSd10 X1] [X2 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2]: 5 steps
lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01678 ▸
       at 1 4 (S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01672 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 4 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01673 ▸
       at 7 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01678 ▸ done

-- pass [X3 CKd30 X3] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 61 steps
lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  b0 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (X3 ∷ Sw01 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  b1 = at 0 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 1 4 (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) wn01677 ▸
       at 0 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b2 : Chain (X2 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  b2 = at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 4 2 [] wn00031 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b3 : Chain (X2 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ [])
  b3 = at 2 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01485 ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 [] wn00003 ▸
       at 1 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b4 : Chain (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ [])
  b4 = at 7 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 3 (X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01485 ▸
       at 5 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ X2 ∷ Sw23 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ X3 ∷ X2 ∷ Sw01 ∷ [])
  b5 = at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 8 2 [] wn00003 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 7 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 2 (Sw01 ∷ CK21⁻ ∷ []) wn00137 ▸ done

  b6 : Chain (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ X3 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ X3 ∷ Sw01 ∷ [])
  b6 = at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 6 4 (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) wn01677 ▸
       at 5 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 6 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 8 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b7 : Chain (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Sw23 ∷ Sw01 ∷ CK21⁻ ∷ Sw23 ∷ X3 ∷ Sw01 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b7 = at 8 2 (CK20⁻ ∷ Sw01 ∷ []) wn00139 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 9 2 [] wn00031 ▸ done

-- pass [CK30] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 25 steps
lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CK30 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK30 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  b0 = at 1 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) wn01407 ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b1 : Chain (X3 ∷ X3 ∷ Sw23 ∷ CK20 ∷ X2 ∷ Sw23 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 [] wn00003 ▸
       at 1 9 (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b2 : Chain (X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ Sw23 ∷ X2 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ [])
  b2 = at 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 8 4 (X2 ∷ CK20 ∷ []) wn01408 ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b3 : Chain (X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ [])
  b3 = at 0 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- pass [X3 CKd31 X3] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 29 steps
lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ Sw23 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ Sw23 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ [])
  b0 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 2 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 4 (X0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01833 ▸
       at 0 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸ done

  b1 : Chain (X0 ∷ Sw23 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ Sw23 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 [] wn00003 ▸
       at 1 3 (X3 ∷ CK31⁻ ∷ X3 ∷ []) wn01834 ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 3 (X3 ∷ CK31⁻ ∷ X3 ∷ []) wn01834 ▸ done

  b2 : Chain (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ Sw23 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ Sw23 ∷ [])
  b2 = at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 7 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 4 (X0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01833 ▸
       at 5 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸ done

  b3 : Chain (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ Sw23 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ Sw23 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  b3 = at 6 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CK31⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 2 [] wn00003 ▸ done

-- pass [X2 CS21 X2] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 5 steps
lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = run b0
  where
  b0 : Chain (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  b0 = at 0 4 (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01689 ▸
       at 1 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 3 (X2 ∷ CS12 ∷ X2 ∷ []) wn01494 ▸
       at 5 4 (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01689 ▸ done

-- pass [X2 CSd21 X2] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 5 steps
lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = run b0
  where
  b0 : Chain (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  b0 = at 0 4 (X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01749 ▸
       at 1 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01500 ▸
       at 1 7 (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102) ▸
       at 5 3 (X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01500 ▸
       at 5 4 (X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01749 ▸ done
