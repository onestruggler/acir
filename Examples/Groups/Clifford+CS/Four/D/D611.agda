{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD611 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D611 (W : Ws) (Sᴰ : SD611) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CCZ123-vs-CS13 : St 1333
  lem-pass-CCZ123-vs-CS13 = pickᴰ 0 Sᴰ
  lem-pass-CCZ123-vs-CSd13 : St 1334
  lem-pass-CCZ123-vs-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-CZ12-vs-CS13 : St 1335
  lem-pass-CZ12-vs-CS13 = pickᴰ 2 Sᴰ
  lem-pass-CZ12-vs-CSd13 : St 1336
  lem-pass-CZ12-vs-CSd13 = pickᴰ 3 Sᴰ
  lem-pass-CZ13-vs-CS13 : St 1337
  lem-pass-CZ13-vs-CS13 = pickᴰ 4 Sᴰ
  lem-pass-CZ13-vs-CSd13 : St 1338
  lem-pass-CZ13-vs-CSd13 = pickᴰ 5 Sᴰ
  lem-pass-Z1-vs-CS13 : St 1339
  lem-pass-Z1-vs-CS13 = pickᴰ 6 Sᴰ
  lem-pass-Z1-vs-CSd13 : St 1340
  lem-pass-Z1-vs-CSd13 = pickᴰ 7 Sᴰ
  lem-pass-CCZ123-vs-CCZ023 : St 922
  lem-pass-CCZ123-vs-CCZ023 = pickᴰ 8 Sᴰ
  lem-pass-CCZ023-vs-CZ13 : St 1256
  lem-pass-CCZ023-vs-CZ13 = pickᴰ 9 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 10 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 11 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 12 Sᴰ
  lem-T-CZ03-T-at1023 : St 1360
  lem-T-CZ03-T-at1023 = pickᴰ 13 Sᴰ
  lem-pass-X1-CS10-X1-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 1366
  lem-pass-X1-CS10-X1-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 14 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 1367
  lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 15 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : St 1368
  lem-pass-X1-CSd10-X1-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = pickᴰ 16 Sᴰ
  lem-pass-X2-CK21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 1369
  lem-pass-X2-CK21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 17 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : St 1370
  lem-pass-X2-CKd21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = pickᴰ 18 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 1371
  lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 19 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : St 1372
  lem-pass-X2-CSd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = pickᴰ 20 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : St 1373
  lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = pickᴰ 21 Sᴰ

private
  q1 : Eqn
  q1 = wE 1681 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 76 W
  q6 : Eqn
  q6 = wE 1499 W
  q7 : Eqn
  q7 = wE 29 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 1482 W
  q10 : Eqn
  q10 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X2 CSd20 X2] [X1 X3 CS03 TOFF012 CSd03 TOFF012 X1 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 0 q1 ∷
   rw 5 q2 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q4 ∷
   rw 2 q5 ∷
   rw⁻ 1 q4 ∷
   rw 2 q6 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q7 ∷
   rw 4 q4 ∷
   rw 5 q8 ∷
   rw 2 q9 ∷
   rw 2 q10 ∷
   rw 6 q9 ∷
   rw 6 q1 ∷
   rw 11 q2 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 9 q4 ∷
   rw 8 q5 ∷
   rw⁻ 7 q4 ∷
   rw 8 q6 ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q7 ∷
   rw 10 q4 ∷
   rw 11 q8 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 1682 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 1493 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 1490 W
  q16 : Eqn
  q16 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X2 CS20 X2] [X1 X3 CS03 TOFF012 CSd03 TOFF012 X1 X3]: 27 steps
lem-pass-X2-CS20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 = derive (X2 ∷ CS02 ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw 0 q11 ∷
   rw 5 q2 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q4 ∷
   rw 2 q12 ∷
   rw⁻ 1 q4 ∷
   rw 2 q13 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q14 ∷
   rw 4 q4 ∷
   rw 5 q8 ∷
   rw 2 q15 ∷
   rw 2 q16 ∷
   rw 6 q15 ∷
   rw 6 q11 ∷
   rw 11 q2 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 9 q4 ∷
   rw 8 q12 ∷
   rw⁻ 7 q4 ∷
   rw 8 q13 ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q14 ∷
   rw 10 q4 ∷
   rw 11 q8 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 1678 W
  q18 : Eqn
  q18 = wE 1671 W
  q19 : Eqn
  q19 = wE 1672 W
  q20 : Eqn
  q20 = sE 1191 lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q21 : Eqn
  q21 = wE 1673 W

-- pass [X1 CSd10 X1] [X2 X3 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q17 ∷
   rw 1 q18 ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 7 q21 ∷
   rw 8 q17 ∷
   rw 9 q18 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 1478 W
  q23 : Eqn
  q23 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q24 : Eqn
  q24 = sE 1370 lem-pass-X2-CKd21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q25 : Eqn
  q25 = wE 1479 W

-- pass [CKd21] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (CK21⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (CK21⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  (rw 0 q22 ∷
   rw 17 q23 ∷
   rw 1 q24 ∷
   rw 15 q25 ∷
   rw⁻ 14 q23 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1476 W
  q27 : Eqn
  q27 = sE 1369 lem-pass-X2-CK21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3
  q28 : Eqn
  q28 = wE 1477 W

-- pass [CK21] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (CK21 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (CK21 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21 ∷ [])
  (rw 0 q26 ∷
   rw 17 q23 ∷
   rw 1 q27 ∷
   rw 15 q28 ∷
   rw⁻ 14 q23 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1812 W
  q30 : Eqn
  q30 = sE 1371 lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q31 : Eqn
  q31 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q32 : Eqn
  q32 = wE 1813 W
  q33 : Eqn
  q33 = wE 1732 W
  q34 : Eqn
  q34 = wE 1814 W

-- CA CSd20 Gad(t=0, W=(3,), d=1, e=1): 7 steps
lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : ⟪ (CS02⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = derive (CS02⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 0 q29 ∷
   rw 1 q30 ∷
   rw 0 q31 ∷
   rw 1 q32 ∷
   rw 6 q33 ∷
   rw 7 q31 ∷
   rw 8 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 1815 W
  q36 : Eqn
  q36 = sE 1372 lem-pass-X2-CSd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3
  q37 : Eqn
  q37 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q38 : Eqn
  q38 = wE 1728 W
  q39 : Eqn
  q39 = wE 1727 W
  q40 : Eqn
  q40 = wE 1816 W

-- CA CS20 Gad(t=0, W=(3,), d=Sd, e=1): 7 steps
lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ : ⟪ (CS02 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ = derive (CS02 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS02 ∷ [])
  (rw 0 q35 ∷
   rw 1 q36 ∷
   rw 0 q37 ∷
   rw 1 q38 ∷
   rw 5 q39 ∷
   rw 5 q37 ∷
   rw 6 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 1817 W
  q42 : Eqn
  q42 = sE 1366 lem-pass-X1-CS10-X1-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q43 : Eqn
  q43 = wE 1818 W

-- CA CSd10 Gad(t=0, W=(3,), d=1, e=1): 7 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : ⟪ (CS01⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = derive (CS01⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS01⁻ ∷ [])
  (rw 0 q41 ∷
   rw 1 q42 ∷
   rw 0 q31 ∷
   rw 1 q32 ∷
   rw 6 q33 ∷
   rw 7 q31 ∷
   rw 8 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 1819 W
  q45 : Eqn
  q45 = sE 1368 lem-pass-X1-CSd10-X1-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3
  q46 : Eqn
  q46 = wE 1820 W

-- CA CS10 Gad(t=0, W=(3,), d=Sd, e=1): 7 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ : ⟪ (CS01 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ = derive (CS01 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS01 ∷ [])
  (rw 0 q44 ∷
   rw 1 q45 ∷
   rw 0 q37 ∷
   rw 1 q38 ∷
   rw 5 q39 ∷
   rw 5 q37 ∷
   rw 6 q46 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 1377 W
  q48 : Eqn
  q48 = wE 127 W
  q49 : Eqn
  q49 = wE 271 W
  q50 : Eqn
  q50 = wE 8 W
  q51 : Eqn
  q51 = wE 9 W
  q52 : Eqn
  q52 = wE 10 W
  q53 : Eqn
  q53 = wE 272 W
  q54 : Eqn
  q54 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q55 : Eqn
  q55 = wE 253 W
  q56 : Eqn
  q56 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q57 : Eqn
  q57 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q58 : Eqn
  q58 = wE 24 W
  q59 : Eqn
  q59 = wE 25 W
  q60 : Eqn
  q60 = wE 26 W
  q61 : Eqn
  q61 = wE 12 W
  q62 : Eqn
  q62 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q63 : Eqn
  q63 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q64 : Eqn
  q64 = wE 14 W
  q65 : Eqn
  q65 = wE 15 W
  q66 : Eqn
  q66 = wE 16 W
  q67 : Eqn
  q67 = wE 46 W
  q68 : Eqn
  q68 = wE 30 W
  q69 : Eqn
  q69 = wE 22 W
  q70 : Eqn
  q70 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q71 : Eqn
  q71 = wE 23 W
  q72 : Eqn
  q72 = wE 47 W
  q73 : Eqn
  q73 = wE 48 W
  q74 : Eqn
  q74 = wE 1 W
  q75 : Eqn
  q75 = wE 3 W
  q76 : Eqn
  q76 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q77 : Eqn
  q77 = wE 43 W
  q78 : Eqn
  q78 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q79 : Eqn
  q79 = wE 20 W
  q80 : Eqn
  q80 = wE 21 W
  q81 : Eqn
  q81 = wE 49 W
  q82 : Eqn
  q82 = wE 50 W
  q83 : Eqn
  q83 = wE 51 W
  q84 : Eqn
  q84 = wE 52 W
  q85 : Eqn
  q85 = sE 1360 lem-T-CZ03-T-at1023
  q86 : Eqn
  q86 = wE 1806 W
  q87 : Eqn
  q87 = wE 1807 W
  q88 : Eqn
  q88 = sE 1256 lem-pass-CCZ023-vs-CZ13
  q89 : Eqn
  q89 = sE 922 lem-pass-CCZ123-vs-CCZ023
  q90 : Eqn
  q90 = wE 1808 W
  q91 : Eqn
  q91 = wE 74 W
  q92 : Eqn
  q92 = wE 33 W
  q93 : Eqn
  q93 = sE 1333 lem-pass-CCZ123-vs-CS13
  q94 : Eqn
  q94 = sE 1337 lem-pass-CZ13-vs-CS13
  q95 : Eqn
  q95 = sE 1335 lem-pass-CZ12-vs-CS13
  q96 : Eqn
  q96 = sE 1339 lem-pass-Z1-vs-CS13
  q97 : Eqn
  q97 = sE 1334 lem-pass-CCZ123-vs-CSd13
  q98 : Eqn
  q98 = sE 1338 lem-pass-CZ13-vs-CSd13
  q99 : Eqn
  q99 = sE 1336 lem-pass-CZ12-vs-CSd13
  q100 : Eqn
  q100 = sE 1340 lem-pass-Z1-vs-CSd13

-- pass [Z1 CZ12 CZ13 CCZ123] [TOFF102 CS13 TOFF102 CSd13]: 526 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 = derive (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 3 q47 ∷
   rw 7 q2 ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q48 ∷
   rw 12 q49 ∷
   rw 11 q12 ∷
   rw 10 q50 ∷
   rw 9 q51 ∷
   rw 8 q50 ∷
   rw 7 q52 ∷
   rw 6 q49 ∷
   rw 7 q53 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q54 ∷
   rw 10 q52 ∷
   rw⁻ 9 q54 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 8 q55 ∷
   rw⁻ 7 q56 ∷
   rw 6 q55 ∷
   rw⁻ 5 q57 ∷
   rw 6 q2 ∷
   rw 7 q57 ∷
   rw 8 q58 ∷
   rw 9 q56 ∷
   rw 10 q58 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q54 ∷
   rw 12 q59 ∷
   rw 13 q54 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q60 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q48 ∷
   rw 10 q49 ∷
   rw 9 q12 ∷
   rw 8 q50 ∷
   rw 7 q51 ∷
   rw 6 q50 ∷
   rw 5 q52 ∷
   rw 4 q49 ∷
   rw 5 q53 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 8 q61 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 14 q62 ∷
   rw 13 q63 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q64 ∷
   rw 11 q61 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q65 ∷
   rw 9 q61 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q66 ∷
   rw 7 q63 ∷
   rw 8 q67 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q57 ∷
   rw 7 q68 ∷
   rw 8 q56 ∷
   rw 9 q68 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q54 ∷
   rw 11 q14 ∷
   rw 12 q54 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q8 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q69 ∷
   rw 12 q70 ∷
   rw 10 q71 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 11 q64 ∷
   rw 8 q72 ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q64 ∷
   rw 6 q73 ∷
   rw 7 q74 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q75 ∷
   rw⁻ 9 q76 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q75 ∷
   rw⁻ 11 q76 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q75 ∷
   rw 8 q77 ∷
   re 8 5 (CCZ012 ∷ []) ∷
   re 7 3 (CCZ013 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 12 q62 ∷
   rw 11 q63 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q64 ∷
   rw 9 q61 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q65 ∷
   rw 7 q61 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q66 ∷
   rw 5 q63 ∷
   rw 6 q67 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 6 q78 ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q74 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q76 ∷
   rw 10 q74 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q76 ∷
   rw 12 q74 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q75 ∷
   rw 5 q79 ∷
   rw 8 q61 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 q80 ∷
   rw 10 q61 ∷
   re 8 3 (CX02 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q69 ∷
   rw⁻ 11 q70 ∷
   rw 12 q71 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q57 ∷
   rw 7 q58 ∷
   rw 8 q56 ∷
   rw 9 q58 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q54 ∷
   rw 11 q59 ∷
   rw 12 q54 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q60 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q81 ∷
   rw 7 q82 ∷
   rw 8 q83 ∷
   rw 9 q82 ∷
   rw 10 q79 ∷
   rw 6 q84 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   rw 7 q64 ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q57 ∷
   rw 6 q68 ∷
   rw 7 q56 ∷
   rw 8 q68 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q14 ∷
   rw 11 q54 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q8 ∷
   rw 4 q57 ∷
   rw 5 q58 ∷
   rw 6 q56 ∷
   rw 7 q58 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q59 ∷
   rw 10 q54 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q60 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q57 ∷
   rw 6 q68 ∷
   rw 7 q56 ∷
   rw 8 q68 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q14 ∷
   rw 11 q54 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q57 ∷
   rw 7 q58 ∷
   rw 8 q56 ∷
   rw 9 q58 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q54 ∷
   rw 11 q59 ∷
   rw 12 q54 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q60 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   rw 6 q8 ∷
   rw 2 q47 ∷
   rw 3 q85 ∷
   rw 1 q86 ∷
   rw 0 q87 ∷
   rw 5 q88 ∷
   rw 7 q89 ∷
   rw 2 q90 ∷
   rw 6 q2 ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q57 ∷
   rw 6 q68 ∷
   rw 7 q56 ∷
   rw 8 q68 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q14 ∷
   rw 11 q54 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q8 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q54 ∷
   rw 10 q12 ∷
   rw⁻ 9 q54 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q91 ∷
   rw⁻ 7 q56 ∷
   rw 6 q91 ∷
   rw⁻ 5 q57 ∷
   rw 6 q60 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q57 ∷
   rw 5 q68 ∷
   rw 6 q56 ∷
   rw 7 q68 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q14 ∷
   rw 10 q54 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q8 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q54 ∷
   rw 9 q12 ∷
   rw⁻ 8 q54 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q91 ∷
   rw⁻ 6 q56 ∷
   rw 5 q91 ∷
   rw⁻ 4 q57 ∷
   rw 5 q60 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 5 q92 ∷
   rw 4 q8 ∷
   rw 4 q93 ∷
   rw 3 q94 ∷
   rw 2 q95 ∷
   rw 1 q96 ∷
   rw 5 q47 ∷
   rw 9 q2 ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 15 q48 ∷
   rw 14 q49 ∷
   rw 13 q12 ∷
   rw 12 q50 ∷
   rw 11 q51 ∷
   rw 10 q50 ∷
   rw 9 q52 ∷
   rw 8 q49 ∷
   rw 9 q53 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q54 ∷
   rw 12 q52 ∷
   rw⁻ 11 q54 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 10 q55 ∷
   rw⁻ 9 q56 ∷
   rw 8 q55 ∷
   rw⁻ 7 q57 ∷
   rw 8 q2 ∷
   rw 9 q57 ∷
   rw 10 q58 ∷
   rw 11 q56 ∷
   rw 12 q58 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q54 ∷
   rw 14 q59 ∷
   rw 15 q54 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q60 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q48 ∷
   rw 12 q49 ∷
   rw 11 q12 ∷
   rw 10 q50 ∷
   rw 9 q51 ∷
   rw 8 q50 ∷
   rw 7 q52 ∷
   rw 6 q49 ∷
   rw 7 q53 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 10 q61 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 16 q62 ∷
   rw 15 q63 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q64 ∷
   rw 13 q61 ∷
   re 14 3 (CX02 ∷ []) ∷
   rw 12 q65 ∷
   rw 11 q61 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q66 ∷
   rw 9 q63 ∷
   rw 10 q67 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q57 ∷
   rw 9 q68 ∷
   rw 10 q56 ∷
   rw 11 q68 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q54 ∷
   rw 13 q14 ∷
   rw 14 q54 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q8 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q69 ∷
   rw 14 q70 ∷
   rw 12 q71 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 13 q64 ∷
   rw 10 q72 ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 11 q64 ∷
   rw 8 q73 ∷
   rw 9 q74 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q75 ∷
   rw⁻ 11 q76 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q75 ∷
   rw⁻ 13 q76 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q75 ∷
   rw 10 q77 ∷
   re 10 5 (CCZ012 ∷ []) ∷
   re 9 3 (CCZ013 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 14 q62 ∷
   rw 13 q63 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q64 ∷
   rw 11 q61 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q65 ∷
   rw 9 q61 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q66 ∷
   rw 7 q63 ∷
   rw 8 q67 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 8 q78 ∷
   re 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q74 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q76 ∷
   rw 12 q74 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q76 ∷
   rw 14 q74 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q75 ∷
   rw 7 q79 ∷
   rw 10 q61 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 9 q80 ∷
   rw 12 q61 ∷
   re 10 3 (CX02 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q69 ∷
   rw⁻ 13 q70 ∷
   rw 14 q71 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q57 ∷
   rw 9 q58 ∷
   rw 10 q56 ∷
   rw 11 q58 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q54 ∷
   rw 13 q59 ∷
   rw 14 q54 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q60 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q81 ∷
   rw 9 q82 ∷
   rw 10 q83 ∷
   rw 11 q82 ∷
   rw 12 q79 ∷
   rw 8 q84 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   rw 9 q64 ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q57 ∷
   rw 8 q68 ∷
   rw 9 q56 ∷
   rw 10 q68 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q54 ∷
   rw 12 q14 ∷
   rw 13 q54 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q8 ∷
   rw 6 q57 ∷
   rw 7 q58 ∷
   rw 8 q56 ∷
   rw 9 q58 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q54 ∷
   rw 11 q59 ∷
   rw 12 q54 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q60 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q57 ∷
   rw 8 q68 ∷
   rw 9 q56 ∷
   rw 10 q68 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q54 ∷
   rw 12 q14 ∷
   rw 13 q54 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q57 ∷
   rw 9 q58 ∷
   rw 10 q56 ∷
   rw 11 q58 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q54 ∷
   rw 13 q59 ∷
   rw 14 q54 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q60 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   rw 8 q8 ∷
   rw 4 q47 ∷
   rw 5 q85 ∷
   rw 3 q86 ∷
   rw 2 q87 ∷
   rw 7 q88 ∷
   rw 9 q89 ∷
   rw 4 q90 ∷
   rw 8 q2 ∷
   re 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q57 ∷
   rw 8 q68 ∷
   rw 9 q56 ∷
   rw 10 q68 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q54 ∷
   rw 12 q14 ∷
   rw 13 q54 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q8 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q54 ∷
   rw 12 q12 ∷
   rw⁻ 11 q54 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q91 ∷
   rw⁻ 9 q56 ∷
   rw 8 q91 ∷
   rw⁻ 7 q57 ∷
   rw 8 q60 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q57 ∷
   rw 7 q68 ∷
   rw 8 q56 ∷
   rw 9 q68 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q54 ∷
   rw 11 q14 ∷
   rw 12 q54 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q8 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q54 ∷
   rw 11 q12 ∷
   rw⁻ 10 q54 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q91 ∷
   rw⁻ 8 q56 ∷
   rw 7 q91 ∷
   rw⁻ 6 q57 ∷
   rw 7 q60 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   rw 7 q92 ∷
   rw 6 q8 ∷
   rw 6 q97 ∷
   rw 5 q98 ∷
   rw 4 q99 ∷
   rw 3 q100 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q102 : Eqn
  q102 = wE 173 W
  q103 : Eqn
  q103 = wE 1464 W
  q104 : Eqn
  q104 = wE 175 W
  q105 : Eqn
  q105 = sE 1373 lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2
  q106 : Eqn
  q106 = wE 1465 W

-- pass [CKd30] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 27 steps
lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 2 q23 ∷
   rw 1 q101 ∷
   rw 2 q74 ∷
   rw 1 q102 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q75 ∷
   rw 1 q103 ∷
   rw 0 q104 ∷
   rw 1 q104 ∷
   rw 4 q74 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q104 ∷
   rw 4 q75 ∷
   rw 1 q105 ∷
   rw 13 q74 ∷
   rw 12 q102 ∷
   rw 11 q102 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q75 ∷
   rw 9 q102 ∷
   rw 10 q106 ∷
   rw 9 q104 ∷
   rw 12 q74 ∷
   re 10 3 (CK30⁻ ∷ []) ∷
   rw 11 q75 ∷
   rw⁻ 0 q101 ∷
   rw⁻ 1 q23 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = wE 1821 W
  q108 : Eqn
  q108 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q109 : Eqn
  q109 = sE 1367 lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q110 : Eqn
  q110 = wE 1822 W

-- pass [CSd10] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  (rw 0 q107 ∷
   rw 10 q108 ∷
   rw 11 q101 ∷
   rw 1 q109 ∷
   rw 9 q110 ∷
   rw⁻ 8 q101 ∷
   rw⁻ 7 q108 ∷ []) Eq.refl
