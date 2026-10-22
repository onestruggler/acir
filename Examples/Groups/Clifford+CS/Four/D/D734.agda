{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD734 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D734 (W : Ws) (Sᴰ : SD734) where

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
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 1 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 2 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 3 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 4 Sᴰ
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2240
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 5 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2244
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2245
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 7 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2277
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 8 Sᴰ
  lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2278
  lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 9 Sᴰ
  lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 2279
  lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 10 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2280
  lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 11 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2272
  lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 12 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2281
  lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 13 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2275
  lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 14 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2282
  lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 15 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2267
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 16 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2283
  lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 17 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2276
  lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 18 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = wE 137 W
  q5 : Eqn
  q5 = wE 1497 W
  q6 : Eqn
  q6 = wE 139 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 2104 W
  q9 : Eqn
  q9 = sE 2244 lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q10 : Eqn
  q10 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q11 : Eqn
  q11 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q12 : Eqn
  q12 = wE 2105 W

-- pass [X2 CKd20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 29 steps
lem-pass-X2-CKd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   rw 1 q5 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   rw 1 q8 ∷
   rw 15 q9 ∷
   rw 12 q10 ∷
   rw 9 q10 ∷
   rw 6 q11 ∷
   rw 3 q10 ∷
   rw 7 q12 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q3 ∷
   rw 10 q4 ∷
   rw⁻ 9 q3 ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   rw 10 q3 ∷
   rw 11 q6 ∷
   rw 12 q3 ∷
   rw 13 q7 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1407 W
  q14 : Eqn
  q14 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q15 : Eqn
  q15 = sE 2279 lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q16 : Eqn
  q16 = wE 1408 W

-- pass [CK20] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (CK20 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (CK20 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ [])
  (rw 0 q13 ∷
   rw 13 q14 ∷
   rw 1 q15 ∷
   rw 11 q16 ∷
   rw⁻ 10 q14 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = wE 1493 W
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = wE 2106 W
  q21 : Eqn
  q21 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q22 : Eqn
  q22 = wE 2107 W

-- pass [X2 CS20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 27 steps
lem-pass-X2-CS20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q3 ∷
   rw 1 q17 ∷
   rw⁻ 0 q3 ∷
   rw 1 q18 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q19 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   rw 1 q20 ∷
   rw 9 q21 ∷
   rw 6 q9 ∷
   rw 3 q21 ∷
   rw 7 q22 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q3 ∷
   rw 10 q17 ∷
   rw⁻ 9 q3 ∷
   rw 10 q18 ∷
   rw 9 q2 ∷
   rw 10 q3 ∷
   rw 11 q19 ∷
   rw 12 q3 ∷
   rw 13 q7 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 2111 W
  q24 : Eqn
  q24 = sE 2267 lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q25 : Eqn
  q25 = wE 2112 W

-- pass [CS31] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 3 steps
lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ [])
  (rw 0 q23 ∷
   rw 1 q24 ∷
   rw 5 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1 W
  q27 : Eqn
  q27 = wE 173 W
  q28 : Eqn
  q28 = wE 3 W
  q29 : Eqn
  q29 = wE 1482 W
  q30 : Eqn
  q30 = wE 175 W
  q31 : Eqn
  q31 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q32 : Eqn
  q32 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q33 : Eqn
  q33 = wE 1483 W
  q34 : Eqn
  q34 = sE 2283 lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q35 : Eqn
  q35 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q36 : Eqn
  q36 = eqn (K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap))
  q37 : Eqn
  q37 = wE 1484 W

-- pass [X3 CSd30 X3] [S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1]: 53 steps
lem-pass-X3-CSd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q29 ∷
   rw 0 q30 ∷
   rw 3 q26 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q28 ∷
   rw 5 q26 ∷
   rw 4 q31 ∷
   rw 3 q32 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q33 ∷
   rw⁻ 0 q32 ∷
   rw⁻ 1 q31 ∷
   rw 2 q30 ∷
   rw 5 q26 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q28 ∷
   rw 2 q34 ∷
   rw 11 q26 ∷
   rw 10 q35 ∷
   rw 9 q36 ∷
   rw 8 q27 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q28 ∷
   rw 6 q27 ∷
   rw 7 q37 ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q35 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   rw 8 q27 ∷
   rw 9 q29 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 1485 W
  q39 : Eqn
  q39 = wE 1486 W
  q40 : Eqn
  q40 = sE 2281 lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q41 : Eqn
  q41 = wE 1487 W

-- pass [X3 CKd30 X3] [S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1]: 53 steps
lem-pass-X3-CKd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q38 ∷
   rw 0 q30 ∷
   rw 3 q26 ∷
   re 1 3 (CK30⁻ ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q28 ∷
   rw 5 q26 ∷
   rw 4 q31 ∷
   rw 3 q32 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q39 ∷
   rw⁻ 0 q32 ∷
   rw⁻ 1 q31 ∷
   rw 2 q30 ∷
   rw 5 q26 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q28 ∷
   rw 2 q40 ∷
   rw 11 q26 ∷
   rw 10 q35 ∷
   rw 9 q36 ∷
   rw 8 q27 ∷
   re 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q28 ∷
   rw 6 q27 ∷
   rw 7 q41 ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q35 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   rw 8 q27 ∷
   rw 9 q38 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 1413 W
  q43 : Eqn
  q43 = wE 1488 W
  q44 : Eqn
  q44 = sE 2280 lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q45 : Eqn
  q45 = wE 1489 W

-- pass [X3 CK30 X3] [S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1]: 53 steps
lem-pass-X3-CK30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = derive (X3 ∷ CK30 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q42 ∷
   rw 0 q30 ∷
   rw 3 q26 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q28 ∷
   rw 5 q26 ∷
   rw 4 q31 ∷
   rw 3 q32 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q43 ∷
   rw⁻ 0 q32 ∷
   rw⁻ 1 q31 ∷
   rw 2 q30 ∷
   rw 5 q26 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q28 ∷
   rw 2 q44 ∷
   rw 11 q26 ∷
   rw 10 q35 ∷
   rw 9 q36 ∷
   rw 8 q27 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q28 ∷
   rw 6 q27 ∷
   rw 7 q45 ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q35 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   rw 8 q27 ∷
   rw 9 q42 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1490 W
  q47 : Eqn
  q47 = wE 1491 W
  q48 : Eqn
  q48 = sE 2282 lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q49 : Eqn
  q49 = wE 1492 W

-- pass [X3 CS30 X3] [S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1]: 53 steps
lem-pass-X3-CS30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1 = derive (X3 ∷ CS03 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q46 ∷
   rw 0 q30 ∷
   rw 3 q26 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q28 ∷
   rw 5 q26 ∷
   rw 4 q31 ∷
   rw 3 q32 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q47 ∷
   rw⁻ 0 q32 ∷
   rw⁻ 1 q31 ∷
   rw 2 q30 ∷
   rw 5 q26 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q28 ∷
   rw 2 q48 ∷
   rw 11 q26 ∷
   rw 10 q35 ∷
   rw 9 q36 ∷
   rw 8 q27 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q28 ∷
   rw 6 q27 ∷
   rw 7 q49 ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q35 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   rw 8 q27 ∷
   rw 9 q46 ∷
   rw 8 q30 ∷
   rw 11 q26 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q28 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 1376 W
  q51 : Eqn
  q51 = wE 1377 W
  q52 : Eqn
  q52 = wE 1378 W
  q53 : Eqn
  q53 = sE 2245 lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q54 : Eqn
  q54 = wE 1379 W
  q55 : Eqn
  q55 = wE 1380 W
  q56 : Eqn
  q56 = wE 1381 W

-- pass [X2 CKd21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 0 q50 ∷
   rw 1 q51 ∷
   rw 2 q52 ∷
   rw 3 q51 ∷
   rw⁻ 4 q53 ∷
   rw 10 q54 ∷
   rw 9 q55 ∷
   rw 8 q56 ∷
   rw 7 q55 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 2262 W
  q58 : Eqn
  q58 = wE 2263 W
  q59 : Eqn
  q59 = sE 2240 lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q60 : Eqn
  q60 = sE 1175 lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q61 : Eqn
  q61 = wE 2264 W

-- ca-split Gad(t=0, W=(), d=SK, e=-1) 1: 5 steps
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-1 : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CK10 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK10⁻ ∷ CS01⁻ ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-1 = derive (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS01 ∷ CK10 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK10⁻ ∷ CS01⁻ ∷ [])
  (rw 0 q57 ∷
   rw 12 q58 ∷
   rw 5 q59 ∷
   rw 2 q60 ∷
   rw 6 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 1357 W
  q63 : Eqn
  q63 = wE 45 W
  q64 : Eqn
  q64 = wE 231 W
  q65 : Eqn
  q65 = sE 2278 lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q66 : Eqn
  q66 = wE 1358 W
  q67 : Eqn
  q67 = wE 227 W
  q68 : Eqn
  q68 = wE 1342 W

-- pass [X1 CKd10 X1] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 0 q26 ∷
   rw 1 q62 ∷
   rw 2 q26 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q26 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q28 ∷
   rw 1 q63 ∷
   rw 2 q26 ∷
   rw 3 q64 ∷
   rw 4 q26 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q26 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q28 ∷
   rw 3 q63 ∷
   rw⁻ 4 q65 ∷
   rw 12 q26 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q28 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q28 ∷
   rw 11 q66 ∷
   rw 10 q28 ∷
   rw 9 q67 ∷
   rw 10 q26 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q28 ∷
   rw 9 q68 ∷
   rw 8 q28 ∷
   rw 7 q67 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = sE 2277 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3

-- pass [CS03 TOFF012 CSd03 TOFF012] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 33 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 14 q63 ∷
   rw 15 q26 ∷
   rw 16 q62 ∷
   rw 17 q26 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q26 ∷
   re 16 3 (CS03⁻ ∷ []) ∷
   rw 17 q28 ∷
   rw 16 q63 ∷
   rw 17 q26 ∷
   rw 18 q64 ∷
   rw 19 q26 ∷
   re 17 3 (CS03⁻ ∷ []) ∷
   rw 20 q26 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q28 ∷
   rw⁻ 4 q69 ∷
   rw 3 q67 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q28 ∷
   rw 3 q66 ∷
   rw 2 q28 ∷
   rw 1 q67 ∷
   rw 2 q26 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q28 ∷
   rw 1 q68 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 1678 W
  q71 : Eqn
  q71 = wE 1671 W
  q72 : Eqn
  q72 = wE 2265 W
  q73 : Eqn
  q73 = sE 1191 lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q74 : Eqn
  q74 = wE 2266 W

-- pass [X1 CSd10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 9 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q70 ∷
   rw 1 q71 ∷
   rw 2 q72 ∷
   rw 12 q73 ∷
   rw 9 q59 ∷
   rw 6 q73 ∷
   rw 10 q74 ∷
   rw 14 q70 ∷
   rw 15 q71 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 2267 W
  q76 : Eqn
  q76 = wE 2268 W
  q77 : Eqn
  q77 = wE 2269 W
  q78 : Eqn
  q78 = wE 2270 W

-- pass [X1 CKd10 X1] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 11 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw 0 q75 ∷
   rw 1 q76 ∷
   rw 2 q77 ∷
   rw 18 q59 ∷
   rw 15 q60 ∷
   rw 12 q60 ∷
   rw 9 q59 ∷
   rw 6 q73 ∷
   rw 10 q78 ∷
   rw 14 q75 ∷
   rw 15 q76 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q80 : Eqn
  q80 = eqn (Sw01 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI)))
  q81 : Eqn
  q81 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q82 : Eqn
  q82 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q83 : Eqn
  q83 = wE 76 W
  q84 : Eqn
  q84 = wE 2271 W
  q85 : Eqn
  q85 = wE 29 W
  q86 : Eqn
  q86 = sE 2276 lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q87 : Eqn
  q87 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q88 : Eqn
  q88 = wE 2272 W

-- pass [X3 CSd30 X3] [Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2]: 73 steps
lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q29 ∷
   rw 0 q30 ∷
   rw 3 q26 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q28 ∷
   rw 7 q1 ∷
   rw⁻ 6 q79 ∷
   rw⁻ 5 q79 ∷
   rw⁻ 4 q80 ∷
   rw⁻ 3 q81 ∷
   rw⁻ 2 q2 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q82 ∷
   rw 2 q83 ∷
   rw⁻ 1 q82 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 1 q84 ∷
   rw 0 q81 ∷
   rw 1 q80 ∷
   rw 2 q79 ∷
   rw 3 q79 ∷
   rw 4 q2 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q82 ∷
   rw 6 q85 ∷
   rw 7 q82 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q7 ∷
   rw 4 q86 ∷
   rw 15 q1 ∷
   rw⁻ 14 q79 ∷
   rw⁻ 13 q87 ∷
   rw⁻ 12 q81 ∷
   rw⁻ 11 q81 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q82 ∷
   rw 10 q83 ∷
   rw⁻ 9 q82 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 9 q88 ∷
   rw 8 q81 ∷
   rw 9 q81 ∷
   rw 10 q87 ∷
   rw 11 q79 ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q82 ∷
   rw 14 q85 ∷
   rw 15 q82 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q7 ∷
   rw 15 q26 ∷
   rw 14 q27 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q28 ∷
   rw 12 q27 ∷
   rw 13 q29 ∷
   rw 12 q30 ∷
   rw 15 q26 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 14 q30 ∷
   rw 15 q28 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 2273 W
  q90 : Eqn
  q90 = sE 2275 lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q91 : Eqn
  q91 = wE 2274 W

-- pass [X3 CKd30 X3] [Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2]: 73 steps
lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q38 ∷
   rw 0 q30 ∷
   rw 3 q26 ∷
   re 1 3 (CK30⁻ ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q28 ∷
   rw 7 q1 ∷
   rw⁻ 6 q79 ∷
   rw⁻ 5 q79 ∷
   rw⁻ 4 q80 ∷
   rw⁻ 3 q81 ∷
   rw⁻ 2 q2 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q82 ∷
   rw 2 q4 ∷
   rw⁻ 1 q82 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 1 q89 ∷
   rw 0 q81 ∷
   rw 1 q80 ∷
   rw 2 q79 ∷
   rw 3 q79 ∷
   rw 4 q2 ∷
   re 6 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q82 ∷
   rw 6 q6 ∷
   rw 7 q82 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q7 ∷
   rw 4 q90 ∷
   rw 15 q1 ∷
   rw⁻ 14 q79 ∷
   rw⁻ 13 q87 ∷
   rw⁻ 12 q81 ∷
   rw⁻ 11 q81 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q82 ∷
   rw 10 q4 ∷
   rw⁻ 9 q82 ∷
   re 10 3 (CK31⁻ ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 9 q91 ∷
   rw 8 q81 ∷
   rw 9 q81 ∷
   rw 10 q87 ∷
   rw 11 q79 ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q82 ∷
   rw 14 q6 ∷
   rw 15 q82 ∷
   re 13 3 (CK30⁻ ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q7 ∷
   rw 15 q26 ∷
   rw 14 q27 ∷
   re 13 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q28 ∷
   rw 12 q27 ∷
   rw 13 q38 ∷
   rw 12 q30 ∷
   rw 15 q26 ∷
   re 13 3 (CK30⁻ ∷ []) ∷
   rw 14 q30 ∷
   rw 15 q28 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 140 W
  q93 : Eqn
  q93 = wE 2275 W
  q94 : Eqn
  q94 = wE 142 W
  q95 : Eqn
  q95 = sE 2272 lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q96 : Eqn
  q96 = wE 2276 W

-- pass [X3 CK30 X3] [Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2]: 73 steps
lem-pass-X3-CK30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2 = derive (X3 ∷ CK30 ∷ X3 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ []) (S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q27 ∷
   rw 1 q42 ∷
   rw 0 q30 ∷
   rw 3 q26 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q28 ∷
   rw 7 q1 ∷
   rw⁻ 6 q79 ∷
   rw⁻ 5 q79 ∷
   rw⁻ 4 q80 ∷
   rw⁻ 3 q81 ∷
   rw⁻ 2 q2 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q82 ∷
   rw 2 q92 ∷
   rw⁻ 1 q82 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 1 q93 ∷
   rw 0 q81 ∷
   rw 1 q80 ∷
   rw 2 q79 ∷
   rw 3 q79 ∷
   rw 4 q2 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q82 ∷
   rw 6 q94 ∷
   rw 7 q82 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q7 ∷
   rw 4 q95 ∷
   rw 15 q1 ∷
   rw⁻ 14 q79 ∷
   rw⁻ 13 q87 ∷
   rw⁻ 12 q81 ∷
   rw⁻ 11 q81 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q82 ∷
   rw 10 q92 ∷
   rw⁻ 9 q82 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 9 q96 ∷
   rw 8 q81 ∷
   rw 9 q81 ∷
   rw 10 q87 ∷
   rw 11 q79 ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q82 ∷
   rw 14 q94 ∷
   rw 15 q82 ∷
   re 13 3 (CK30 ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q7 ∷
   rw 15 q26 ∷
   rw 14 q27 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q28 ∷
   rw 12 q27 ∷
   rw 13 q42 ∷
   rw 12 q30 ∷
   rw 15 q26 ∷
   re 13 3 (CK30 ∷ []) ∷
   rw 14 q30 ∷
   rw 15 q28 ∷ []) Eq.refl
