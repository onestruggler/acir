{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD546 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D546 (W : Ws) (Sᴰ : SD546) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 914
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 0 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 915
  lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 1 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 916
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 2 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 917
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 3 Sᴰ
  lem-AXIOM-LF-at1302 : St 920
  lem-AXIOM-LF-at1302 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q6 : Eqn
  q6 = eqn (X2 ∷ CK21 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1559 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q12 : Eqn
  q12 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1560 W)
  q13 : Eqn
  q13 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q14 : Eqn
  q14 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q15 : Eqn
  q15 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q16 : Eqn
  q16 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1561 W)
  q17 : Eqn
  q17 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q18 : Eqn
  q18 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q19 : Eqn
  q19 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q20 : Eqn
  q20 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1562 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)

-- pass [X2 CK20 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 57 steps
lem-pass-X2-CK20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (X2 ∷ CK20 ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 5 q1 ∷
   rw⁻ 4 q2 ∷
   rw 3 q3 ∷
   rw⁻ 2 q4 ∷
   rw 1 q5 ∷
   rw⁻ 0 q4 ∷
   rw 1 q6 ∷
   rw 0 q7 ∷
   rw 1 q2 ∷
   rw 2 q4 ∷
   rw 3 q8 ∷
   rw 4 q4 ∷
   rw 5 q4 ∷
   rw 6 q9 ∷
   rw 7 q4 ∷
   rw 8 q4 ∷
   rw 9 q10 ∷
   rw 10 q4 ∷
   rw 11 q4 ∷
   rw 12 q9 ∷
   rw 13 q4 ∷
   rw 14 q4 ∷
   rw 15 q8 ∷
   rw 16 q4 ∷
   rw 17 q11 ∷
   rw 2 q12 ∷
   rw 18 q13 ∷
   rw 15 q14 ∷
   rw 12 q15 ∷
   rw 9 q14 ∷
   rw 6 q13 ∷
   rw 10 q16 ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q4 ∷
   rw 27 q17 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 25 q4 ∷
   rw 24 q18 ∷
   rw⁻ 23 q4 ∷
   rw⁻ 22 q4 ∷
   rw 21 q19 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 19 q4 ∷
   rw 18 q18 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 16 q4 ∷
   rw 15 q17 ∷
   rw⁻ 14 q4 ∷
   rw 15 q20 ∷
   rw 14 q7 ∷
   rw 15 q2 ∷
   rw 16 q4 ∷
   rw 17 q21 ∷
   rw 18 q4 ∷
   rw 19 q11 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (X2 ∷ CS12 ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1563 W)
  q23 : Eqn
  q23 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1564 W)
  q24 : Eqn
  q24 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1565 W)
  q25 : Eqn
  q25 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1566 W)

-- pass [X2 CS20 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 43 steps
lem-pass-X2-CS20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (X2 ∷ CS02 ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw 5 q1 ∷
   rw⁻ 4 q2 ∷
   rw 3 q3 ∷
   rw⁻ 2 q4 ∷
   rw 1 q19 ∷
   rw⁻ 0 q4 ∷
   rw 1 q22 ∷
   rw 0 q7 ∷
   rw 1 q2 ∷
   rw 2 q4 ∷
   rw 3 q8 ∷
   rw 4 q4 ∷
   rw 5 q4 ∷
   rw 6 q9 ∷
   rw 7 q4 ∷
   rw 8 q4 ∷
   rw 9 q9 ∷
   rw 10 q4 ∷
   rw 11 q11 ∷
   rw 2 q23 ∷
   rw 12 q14 ∷
   rw 9 q14 ∷
   rw 6 q13 ∷
   rw 10 q24 ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q4 ∷
   rw 21 q18 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 19 q4 ∷
   rw 18 q18 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 16 q4 ∷
   rw 15 q17 ∷
   rw⁻ 14 q4 ∷
   rw 15 q25 ∷
   rw 14 q7 ∷
   rw 15 q2 ∷
   rw 16 q4 ∷
   rw 17 q10 ∷
   rw 18 q4 ∷
   rw 19 q11 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1499 W)
  q27 : Eqn
  q27 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1483 W)
  q28 : Eqn
  q28 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1484 W)

-- pass [X2 CSd20 X2] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 25 steps
lem-pass-X2-CSd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q4 ∷
   rw 1 q17 ∷
   rw⁻ 0 q4 ∷
   rw 1 q26 ∷
   rw 0 q2 ∷
   rw 1 q4 ∷
   rw 2 q8 ∷
   rw 3 q4 ∷
   rw 4 q11 ∷
   rw 1 q27 ∷
   rw 3 q13 ∷
   rw 7 q28 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q4 ∷
   rw 10 q17 ∷
   rw⁻ 9 q4 ∷
   rw 10 q26 ∷
   rw 9 q2 ∷
   rw 10 q4 ∷
   rw 11 q8 ∷
   rw 12 q4 ∷
   rw 13 q11 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1497 W)
  q30 : Eqn
  q30 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1486 W)
  q31 : Eqn
  q31 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1487 W)

-- pass [X2 CKd20 X2] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q4 ∷
   rw 1 q18 ∷
   rw⁻ 0 q4 ∷
   rw 1 q29 ∷
   rw 0 q2 ∷
   rw 1 q4 ∷
   rw 2 q9 ∷
   rw 3 q4 ∷
   rw 4 q11 ∷
   rw 1 q30 ∷
   rw 3 q14 ∷
   rw 7 q31 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q4 ∷
   rw 10 q18 ∷
   rw⁻ 9 q4 ∷
   rw 10 q29 ∷
   rw 9 q2 ∷
   rw 10 q4 ∷
   rw 11 q9 ∷
   rw 12 q4 ∷
   rw 13 q11 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1495 W)
  q33 : Eqn
  q33 = eqn (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1488 W)
  q34 : Eqn
  q34 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q35 : Eqn
  q35 = eqn (X2 ∷ CK20 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1489 W)

-- pass [X2 CK20 X2] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 25 steps
lem-pass-X2-CK20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q4 ∷
   rw 1 q5 ∷
   rw⁻ 0 q4 ∷
   rw 1 q32 ∷
   rw 0 q2 ∷
   rw 1 q4 ∷
   rw 2 q21 ∷
   rw 3 q4 ∷
   rw 4 q11 ∷
   rw 1 q33 ∷
   rw 3 q34 ∷
   rw 7 q35 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q4 ∷
   rw 10 q5 ∷
   rw⁻ 9 q4 ∷
   rw 10 q32 ∷
   rw 9 q2 ∷
   rw 10 q4 ∷
   rw 11 q21 ∷
   rw 12 q4 ∷
   rw 13 q11 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1493 W)
  q37 : Eqn
  q37 = eqn (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1491 W)
  q38 : Eqn
  q38 = eqn (X2 ∷ CS02 ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1492 W)

-- pass [X2 CS20 X2] [X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X3]: 25 steps
lem-pass-X2-CS20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = derive (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q4 ∷
   rw 1 q19 ∷
   rw⁻ 0 q4 ∷
   rw 1 q36 ∷
   rw 0 q2 ∷
   rw 1 q4 ∷
   rw 2 q10 ∷
   rw 3 q4 ∷
   rw 4 q11 ∷
   rw 1 q37 ∷
   rw 3 q15 ∷
   rw 7 q38 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q4 ∷
   rw 10 q19 ∷
   rw⁻ 9 q4 ∷
   rw 10 q36 ∷
   rw 9 q2 ∷
   rw 10 q4 ∷
   rw 11 q10 ∷
   rw 12 q4 ∷
   rw 13 q11 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ Toff203 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Toff203 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (lem-AXIOM-LF-at1302)
  q40 : Eqn
  q40 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)

-- kk pieces X3 CS13 CS13 CK31 CS13 CX30 CS01 CS01 CS01 CK01 S0 CS01 CS01 at 3: 5 steps
lem-kk-pieces-X3-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01-CK01-S0-CS01-CS01-at-3 : ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ
lem-kk-pieces-X3-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01-CK01-S0-CS01-CS01-at-3 = derive (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ [])
  (rw 1 q39 ∷
   rw 30 q40 ∷
   rw 33 q40 ∷
   rw 66 q40 ∷
   rw 69 q40 ∷ []) Eq.refl
