{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD614 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D614 (W : Ws) (Sᴰ : SD614) where

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
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CSd13-vs-CS03 : St 1095
  lem-pass-CSd13-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-CSd13-vs-CSd03 : St 1096
  lem-pass-CSd13-vs-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CS03-vs-S1 : St 663
  lem-pass-CS03-vs-S1 = pickᴰ 4 Sᴰ
  lem-pass-CS03-vs-Sd1 : St 1100
  lem-pass-CS03-vs-Sd1 = pickᴰ 5 Sᴰ
  lem-pass-CSd03-vs-S1 : St 664
  lem-pass-CSd03-vs-S1 = pickᴰ 6 Sᴰ
  lem-pass-CSd03-vs-Sd1 : St 1101
  lem-pass-CSd03-vs-Sd1 = pickᴰ 7 Sᴰ
  lem-pass-TOFF012-vs-S1 : St 1102
  lem-pass-TOFF012-vs-S1 = pickᴰ 8 Sᴰ
  lem-pass-TOFF012-vs-Sd1 : St 1103
  lem-pass-TOFF012-vs-Sd1 = pickᴰ 9 Sᴰ
  lem-pass-TOFF012-vs-X2-TOFF102-X2 : St 1104
  lem-pass-TOFF012-vs-X2-TOFF102-X2 = pickᴰ 10 Sᴰ
  lem-pass-TOFF012-vs-CS13 : St 1119
  lem-pass-TOFF012-vs-CS13 = pickᴰ 11 Sᴰ
  lem-pass-TOFF012-vs-CSd13 : St 1120
  lem-pass-TOFF012-vs-CSd13 = pickᴰ 12 Sᴰ
  lem-pass-TOFF102-vs-CS03 : St 1124
  lem-pass-TOFF102-vs-CS03 = pickᴰ 13 Sᴰ
  lem-pass-TOFF102-vs-CSd03 : St 1125
  lem-pass-TOFF102-vs-CSd03 = pickᴰ 14 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 16 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1195
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 18 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1197
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 19 Sᴰ
  lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 1385
  lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 20 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 1386
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 21 Sᴰ

private
  q1 : Eqn
  q1 = eqn (Toff012 ∷ CS13 ∷ []) (CS13 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CS13)
  q2 : Eqn
  q2 = eqn (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-X2-TOFF102-X2)
  q3 : Eqn
  q3 = eqn (Toff012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CSd13)

-- pass [TOFF012] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 4 steps
lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = derive (Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ [])
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 4 q3 ∷
   rw 5 q2 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = eqn (CS13 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13 ∷ []) lem-pass-CS13-vs-CSd03
  q5 : Eqn
  q5 = eqn (X2 ∷ Toff102 ∷ X2 ∷ []) (CX01 ∷ Toff102 ∷ []) (wn 1359 W)
  q6 : Eqn
  q6 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q7 : Eqn
  q7 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q8 : Eqn
  q8 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q9 : Eqn
  q9 = eqn (CS02⁻ ∷ CX01 ∷ []) (CX01 ∷ CS02⁻ ∷ []) (wn 1748 W)
  q10 : Eqn
  q10 = eqn (Toff102 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff102 ∷ []) lem-pass-TOFF102-vs-CSd03
  q11 : Eqn
  q11 = eqn (CX01 ∷ Toff102 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ []) (wn 1361 W)
  q12 : Eqn
  q12 = eqn (CS13⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13⁻ ∷ []) lem-pass-CSd13-vs-CSd03

-- pass [CSd03] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 26 steps
lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (CS03⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = derive (CS03⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 2 q9 ∷
   rw⁻ 1 q7 ∷
   rw 4 q6 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q8 ∷
   rw⁻ 2 q10 ∷
   rw 1 q11 ∷
   rw⁻ 4 q12 ∷
   rw 6 q5 ∷
   rw 7 q6 ∷
   rw 6 q7 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw⁻ 5 q7 ∷
   rw 8 q6 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q8 ∷
   rw⁻ 6 q10 ∷
   rw 5 q11 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (CS03 ∷ S1 ∷ []) (S1 ∷ CS03 ∷ []) (lem-pass-CS03-vs-S1)
  q14 : Eqn
  q14 = eqn (CS13⁻ ∷ CS03 ∷ []) (CS03 ∷ CS13⁻ ∷ []) lem-pass-CSd13-vs-CS03
  q15 : Eqn
  q15 = eqn (CS02 ∷ CX01 ∷ []) (CX01 ∷ CS02 ∷ []) (wn 1360 W)
  q16 : Eqn
  q16 = eqn (Toff102 ∷ CS03 ∷ []) (CS03 ∷ Toff102 ∷ []) lem-pass-TOFF102-vs-CS03
  q17 : Eqn
  q17 = eqn (CS03 ∷ S1⁻ ∷ []) (S1⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-Sd1)
  q18 : Eqn
  q18 = eqn (CS13 ∷ CS03 ∷ []) (CS03 ∷ CS13 ∷ []) lem-pass-CS13-vs-CS03

-- pass [CS03] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 28 steps
lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (CS03 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = derive (CS03 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ [])
  (rw 0 q13 ∷
   rw⁻ 1 q14 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 3 q15 ∷
   rw⁻ 2 q7 ∷
   rw 5 q6 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q8 ∷
   rw⁻ 3 q16 ∷
   rw 2 q11 ∷
   rw 5 q17 ∷
   rw⁻ 6 q18 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 8 q15 ∷
   rw⁻ 7 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q8 ∷
   rw⁻ 8 q16 ∷
   rw 7 q11 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (Toff012 ∷ S1 ∷ []) (S1 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-S1)
  q20 : Eqn
  q20 = eqn (Toff012 ∷ S1⁻ ∷ []) (S1⁻ ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-Sd1)

-- pass [TOFF012] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 6 steps
lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = derive (Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ [])
  (rw 0 q19 ∷
   rw 1 q3 ∷
   rw 2 q2 ∷
   rw 5 q20 ∷
   rw 6 q1 ∷
   rw 7 q2 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (CS03⁻ ∷ S1 ∷ []) (S1 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-S1)
  q22 : Eqn
  q22 = eqn (CS03⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-Sd1)

-- pass [CSd03] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 28 steps
lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (CS03⁻ ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = derive (CS03⁻ ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ [])
  (rw 0 q21 ∷
   rw⁻ 1 q12 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 3 q9 ∷
   rw⁻ 2 q7 ∷
   rw 5 q6 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q8 ∷
   rw⁻ 3 q10 ∷
   rw 2 q11 ∷
   rw 5 q22 ∷
   rw⁻ 6 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw⁻ 7 q7 ∷
   rw 10 q6 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q8 ∷
   rw⁻ 8 q10 ∷
   rw 7 q11 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (CK20⁻ ∷ []) (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1709 W)
  q24 : Eqn
  q24 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q26 : Eqn
  q26 = eqn (X3 ∷ CK30 ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q27 : Eqn
  q27 = eqn (K0⁻ ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑)))
  q28 : Eqn
  q28 = eqn (K0⁻ ∷ []) (K0⁻ ∷ []) (wn 1710 W)
  q29 : Eqn
  q29 = eqn [] (K0 ∷ K0⁻ ∷ []) (wn 116 W)
  q30 : Eqn
  q30 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q31 : Eqn
  q31 = eqn (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (CK20⁻ ∷ []) (wn 1711 W)

-- CA CKd30 Gad(t=0, W=(2,), d=1, e=-1): 25 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : ⟪ (CK30⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = derive (CK30⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ CK30⁻ ∷ [])
  (rw 1 q6 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q8 ∷
   rw 1 q23 ∷
   rw⁻ 0 q24 ∷
   rw 1 q25 ∷
   rw 4 q6 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q25 ∷
   rw 4 q8 ∷
   rw 1 q26 ∷
   rw 0 q27 ∷
   rw 1 q28 ∷
   rw 6 q29 ∷
   rw 7 q27 ∷
   rw 12 q6 ∷
   rw 11 q30 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw 9 q30 ∷
   rw 8 q24 ∷
   rw 9 q31 ∷
   rw 10 q6 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q34 : Eqn
  q34 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q35 : Eqn
  q35 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q36 : Eqn
  q36 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q37 : Eqn
  q37 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1677 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q40 : Eqn
  q40 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ []) (K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1712 W)
  q41 : Eqn
  q41 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q42 : Eqn
  q42 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q43 : Eqn
  q43 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1713 W)

-- pass [X3 CKd30 X3] [X2 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2]: 65 steps
lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q32 ∷
   rw⁻ 3 q33 ∷
   rw⁻ 2 q34 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q35 ∷
   rw 2 q36 ∷
   rw⁻ 1 q35 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw⁻ 0 q34 ∷
   rw 1 q37 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   re 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q35 ∷
   rw 3 q38 ∷
   rw 4 q35 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q34 ∷
   rw 4 q39 ∷
   rw 5 q6 ∷
   rw 4 q24 ∷
   rw 3 q30 ∷
   re 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 1 q30 ∷
   rw 2 q40 ∷
   rw⁻ 1 q24 ∷
   rw 2 q25 ∷
   rw 5 q6 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   rw 4 q25 ∷
   rw 5 q8 ∷
   rw 2 q41 ∷
   rw 10 q6 ∷
   rw 9 q42 ∷
   rw 8 q30 ∷
   re 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 6 q30 ∷
   rw 7 q43 ∷
   rw⁻ 6 q42 ∷
   rw 7 q25 ∷
   rw 10 q6 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q25 ∷
   rw 10 q8 ∷
   rw 11 q32 ∷
   rw⁻ 10 q33 ∷
   rw⁻ 9 q34 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q35 ∷
   rw 9 q36 ∷
   rw⁻ 8 q35 ∷
   re 9 3 (CK31⁻ ∷ []) ∷
   rw⁻ 7 q34 ∷
   rw 8 q37 ∷
   rw 7 q33 ∷
   rw 8 q34 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw 10 q38 ∷
   rw 11 q35 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q34 ∷
   rw 11 q39 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1680 W)
  q45 : Eqn
  q45 = eqn (X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ []) (wn 1670 W)
  q46 : Eqn
  q46 = eqn (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)

-- pass [X1 CS10 X1] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 5 steps
lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q44 ∷
   rw 1 q45 ∷
   rw 1 q46 ∷
   rw 5 q45 ∷
   rw 5 q44 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1678 W)
  q48 : Eqn
  q48 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1672 W)
  q49 : Eqn
  q49 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q50 : Eqn
  q50 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ []) (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1673 W)

-- pass [X1 CSd10 X1] [X2 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2]: 5 steps
lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q47 ∷
   rw 1 q48 ∷
   rw 2 q49 ∷
   rw 6 q50 ∷
   rw 7 q47 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1485 W)

-- pass [X3 CKd30 X3] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 61 steps
lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q32 ∷
   rw⁻ 3 q33 ∷
   rw⁻ 2 q34 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q35 ∷
   rw 2 q36 ∷
   rw⁻ 1 q35 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw⁻ 0 q34 ∷
   rw 1 q37 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   re 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q35 ∷
   rw 3 q38 ∷
   rw 4 q35 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q34 ∷
   rw 4 q39 ∷
   rw 4 q6 ∷
   rw 3 q30 ∷
   re 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 1 q30 ∷
   rw 2 q51 ∷
   rw 1 q25 ∷
   rw 4 q6 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q25 ∷
   rw 4 q8 ∷
   rw 1 q41 ∷
   rw 8 q6 ∷
   rw 7 q30 ∷
   re 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q30 ∷
   rw 6 q51 ∷
   rw 5 q25 ∷
   rw 8 q6 ∷
   re 6 3 (CK30⁻ ∷ []) ∷
   rw 7 q25 ∷
   rw 8 q8 ∷
   rw 9 q32 ∷
   rw⁻ 8 q33 ∷
   rw⁻ 7 q34 ∷
   re 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q35 ∷
   rw 7 q36 ∷
   rw⁻ 6 q35 ∷
   re 7 3 (CK31⁻ ∷ []) ∷
   rw⁻ 5 q34 ∷
   rw 6 q37 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   rw 8 q38 ∷
   rw 9 q35 ∷
   re 7 3 (CK30⁻ ∷ []) ∷
   rw 8 q34 ∷
   rw 9 q39 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q53 : Eqn
  q53 = eqn (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1407 W)
  q54 : Eqn
  q54 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) (wn 1408 W)

-- pass [CK30] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 25 steps
lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CK30 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CK30 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ [])
  (rw 1 q52 ∷
   rw 2 q6 ∷
   rw 1 q30 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q8 ∷
   rw 1 q53 ∷
   rw 0 q25 ∷
   rw 1 q25 ∷
   rw 4 q6 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q25 ∷
   rw 4 q8 ∷
   rw 1 q26 ∷
   rw 11 q6 ∷
   rw 10 q30 ∷
   rw 9 q30 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q30 ∷
   rw 8 q54 ∷
   rw 7 q25 ∷
   rw 10 q6 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q8 ∷
   rw⁻ 0 q52 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q56 : Eqn
  q56 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1833 W)
  q57 : Eqn
  q57 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1834 W)
  q58 : Eqn
  q58 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X3 CKd31 X3] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 29 steps
lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 4 q6 ∷
   rw 3 q55 ∷
   rw 2 q30 ∷
   re 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 0 q30 ∷
   rw 1 q56 ∷
   rw⁻ 0 q55 ∷
   rw 1 q25 ∷
   rw 4 q6 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw 3 q25 ∷
   rw 4 q8 ∷
   rw 1 q57 ∷
   rw 1 q58 ∷
   rw 5 q57 ∷
   rw 9 q6 ∷
   rw 8 q55 ∷
   rw 7 q30 ∷
   re 6 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q30 ∷
   rw 6 q56 ∷
   rw⁻ 5 q55 ∷
   rw 6 q25 ∷
   rw 9 q6 ∷
   re 7 3 (CK31⁻ ∷ []) ∷
   rw 8 q25 ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1689 W)
  q60 : Eqn
  q60 = eqn (X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ []) (wn 1494 W)
  q61 : Eqn
  q61 = eqn (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X2 CS21 X2] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 5 steps
lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q59 ∷
   rw 1 q60 ∷
   rw 1 q61 ∷
   rw 5 q60 ∷
   rw 5 q59 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1749 W)
  q63 : Eqn
  q63 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1500 W)
  q64 : Eqn
  q64 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X2 CSd21 X2] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 5 steps
lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q62 ∷
   rw 1 q63 ∷
   rw 1 q64 ∷
   rw 5 q63 ∷
   rw 5 q62 ∷ []) Eq.refl
