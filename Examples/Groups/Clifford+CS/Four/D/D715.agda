{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD715 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D715 (W : Ws) (Sᴰ : SD715) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2061
  lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 2 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2062
  lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 3 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2063
  lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2064
  lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 5 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : St 2065
  lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = pickᴰ 6 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2066
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 7 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2067
  lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 8 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : St 2068
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 9 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2069
  lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 10 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2070
  lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 11 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2071
  lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 12 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : St 2072
  lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 13 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 14 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 : St 2073
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 = pickᴰ 16 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 : St 2074
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 = pickᴰ 17 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 : St 2075
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 = pickᴰ 18 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 : St 2076
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 = pickᴰ 19 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 : St 2077
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 = pickᴰ 20 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 : St 2078
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 = pickᴰ 21 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 22 Sᴰ
  lem-S2-at0213-ᵖ-1 : St 2024
  lem-S2-at0213-ᵖ-1 = pickᴰ 23 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 24 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2079
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 25 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 26 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2048
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 27 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 28 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 : St 2054
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 = pickᴰ 29 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 : St 2055
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 = pickᴰ 30 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 : St 2056
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 = pickᴰ 31 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 : St 2080
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 = pickᴰ 32 Sᴰ
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2058
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 33 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2059
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 34 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 2081
  lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 35 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 2082
  lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 36 Sᴰ
  lem-S2-at1023-ᵖ-1 : St 2083
  lem-S2-at1023-ᵖ-1 = pickᴰ 37 Sᴰ
  lem-S2-at1203-ᵖ-1 : St 2084
  lem-S2-at1203-ᵖ-1 = pickᴰ 38 Sᴰ
  lem-S2-at2013-ᵖ-1 : St 2085
  lem-S2-at2013-ᵖ-1 = pickᴰ 39 Sᴰ
  lem-S2-at2103-ᵖ-1 : St 2086
  lem-S2-at2103-ᵖ-1 = pickᴰ 40 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 2087
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 41 Sᴰ
  lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2088
  lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 42 Sᴰ

private
  q1 : Eqn
  q1 = sE 2056 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2
  q2 : Eqn
  q2 = sE 2073 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1
  q3 : Eqn
  q3 = sE 2055 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13
  q4 : Eqn
  q4 = sE 2074 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1
  q5 : Eqn
  q5 = sE 2054 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 X2 S1 CSd13 X2 TOFF102 X2 Sd1 CS13]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 : ⟪ (ℓ "习丽习举丘习丘与举丘习丘丏丽") ⟫ʷ ≈ ⟪ (ℓ "丘习丘与举丘习丘丏丽习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 = derive (ℓ "习丽习举丘习丘与举丘习丘丏丽") (ℓ "丘习丘与举丘习丘丏丽习丽习举")
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q1 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 1499 W
  q7 : Eqn
  q7 = wE 2130 W
  q8 : Eqn
  q8 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q9 : Eqn
  q9 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q10 : Eqn
  q10 = wE 2131 W

-- pass [X2 CSd21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "丘丷丘丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "丘丷丘丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞丘丷丘")
  (rw 0 q6 ∷
   rw 1 q7 ∷
   rw 9 q8 ∷
   rw 6 q9 ∷
   rw 3 q8 ∷
   rw 7 q10 ∷
   rw 9 q6 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 1495 W
  q12 : Eqn
  q12 = wE 2132 W
  q13 : Eqn
  q13 = wE 2133 W

-- pass [X2 CK21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 9 steps
lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "丘乇丘丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "丘乇丘丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞丘乇丘")
  (rw 0 q11 ∷
   rw 1 q12 ∷
   rw 15 q9 ∷
   rw 12 q8 ∷
   rw 9 q8 ∷
   rw 6 q9 ∷
   rw 3 q8 ∷
   rw 7 q13 ∷
   rw 9 q11 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 2079 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "九中九丮丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "九中九丮丞中九丮九丞") (ℓ "丞中九丮九丞九中九丮")
  (rw⁻ 0 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 1520 W
  q16 : Eqn
  q16 = wE 1521 W
  q17 : Eqn
  q17 = wE 1522 W
  q18 : Eqn
  q18 = sE 2081 lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q19 : Eqn
  q19 = wE 1523 W
  q20 : Eqn
  q20 = wE 1524 W
  q21 : Eqn
  q21 = wE 1525 W

-- pass [X3 CS32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞义丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞义丞义乣乊乣") (ℓ "义乣乊乣丞义丞")
  (rw 0 q15 ∷
   rw 1 q16 ∷
   rw 2 q17 ∷
   rw 3 q16 ∷
   rw⁻ 4 q18 ∷
   rw 10 q19 ∷
   rw 9 q20 ∷
   rw 8 q21 ∷
   rw 7 q20 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 2082 lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [X3 CSd32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞乊丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞乊丞") ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞乊丞义乣乊乣") (ℓ "义乣乊乣丞乊丞")
  (rw 0 q15 ∷
   rw 1 q16 ∷
   rw 2 q17 ∷
   rw 3 q16 ∷
   rw⁻ 4 q22 ∷
   rw 10 q19 ∷
   rw 9 q20 ∷
   rw 8 q21 ∷
   rw 7 q20 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 2080 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3
  q24 : Eqn
  q24 = sE 2075 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02
  q25 : Eqn
  q25 = sE 2076 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02

-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (ℓ "乣义乣乊丞乞丞丧丞乞丞丨") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞丧丞乞丞丨乣义乣乊") ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (ℓ "乣义乣乊丞乞丞丧丞乞丞丨") (ℓ "丞乞丞丧丞乞丞丨乣义乣乊")
  (rw 0 q23 ∷
   rw 3 q24 ∷
   rw 4 q23 ∷
   rw 7 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1376 W
  q27 : Eqn
  q27 = wE 1377 W
  q28 : Eqn
  q28 = wE 1378 W
  q29 : Eqn
  q29 = sE 2048 lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q30 : Eqn
  q30 = wE 1379 W
  q31 : Eqn
  q31 = wE 1380 W
  q32 : Eqn
  q32 = wE 1381 W

-- pass [X3 CS31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞丽丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞丽丞丽习举习") (ℓ "丽习举习丞丽丞")
  (rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q27 ∷
   rw⁻ 4 q29 ∷
   rw 10 q30 ∷
   rw 9 q31 ∷
   rw 8 q32 ∷
   rw 7 q31 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 1 W
  q34 : Eqn
  q34 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q35 : Eqn
  q35 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q36 : Eqn
  q36 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q37 : Eqn
  q37 = wE 173 W
  q38 : Eqn
  q38 = wE 3 W
  q39 : Eqn
  q39 = wE 2134 W
  q40 : Eqn
  q40 = wE 175 W
  q41 : Eqn
  q41 = sE 2049 lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q42 : Eqn
  q42 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q43 : Eqn
  q43 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q44 : Eqn
  q44 = wE 2135 W

-- pass [X3 CSd30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 57 steps
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞丮丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞丮丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞丮丞")
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q39 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (ℓ "丮") ∷
   rw 12 q40 ∷
   rw 13 q38 ∷
   rw 10 q41 ∷
   rw 7 q42 ∷
   rw 4 q41 ∷
   rw 21 q33 ∷
   rw 20 q34 ∷
   rw 19 q43 ∷
   rw 18 q36 ∷
   rw 17 q36 ∷
   rw 16 q37 ∷
   re 15 1 (ℓ "乏丨乏") ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q44 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (ℓ "丮") ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 2136 W
  q46 : Eqn
  q46 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q47 : Eqn
  q47 = wE 2137 W

-- pass [X3 CKd30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 75 steps
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞乒丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞乒丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞乒丞")
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q45 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q40 ∷
   rw 13 q40 ∷
   rw 16 q33 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q40 ∷
   rw 16 q40 ∷
   rw 19 q33 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q40 ∷
   rw 19 q38 ∷
   rw 16 q42 ∷
   rw 13 q46 ∷
   rw 10 q46 ∷
   rw 7 q42 ∷
   rw 4 q41 ∷
   rw 27 q33 ∷
   rw 26 q34 ∷
   rw 25 q43 ∷
   rw 24 q36 ∷
   rw 23 q36 ∷
   rw 22 q37 ∷
   re 21 1 (ℓ "乏乄乏") ∷
   rw 23 q38 ∷
   rw 20 q37 ∷
   rw 19 q37 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q38 ∷
   rw 17 q37 ∷
   rw 16 q37 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q47 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (ℓ "乒") ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 2138 W
  q49 : Eqn
  q49 = sE 1146 lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q50 : Eqn
  q50 = wE 2139 W

-- pass [X3 CK30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 75 steps
lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞乑丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞乑丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞乑丞")
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q48 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (ℓ "乒") ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q40 ∷
   rw 13 q40 ∷
   rw 16 q33 ∷
   re 14 3 (ℓ "乒") ∷
   rw 15 q40 ∷
   rw 16 q40 ∷
   rw 19 q33 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q40 ∷
   rw 19 q38 ∷
   rw 16 q46 ∷
   rw 13 q49 ∷
   rw 10 q46 ∷
   rw 7 q46 ∷
   rw 4 q49 ∷
   rw 27 q33 ∷
   rw 26 q34 ∷
   rw 25 q43 ∷
   rw 24 q36 ∷
   rw 23 q36 ∷
   rw 22 q37 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q38 ∷
   rw 20 q37 ∷
   rw 19 q37 ∷
   re 18 1 (ℓ "乏久乏") ∷
   rw 20 q38 ∷
   rw 17 q37 ∷
   rw 16 q37 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (ℓ "乏久乏") ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q50 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = wE 2140 W
  q52 : Eqn
  q52 = wE 2141 W

-- pass [X3 CS30 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 57 steps
lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞中丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞中丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞中丞")
  (rw 7 q33 ∷
   rw 6 q34 ∷
   rw 5 q34 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q38 ∷
   rw 0 q37 ∷
   rw 1 q51 ∷
   rw⁻ 0 q36 ∷
   rw⁻ 1 q35 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q34 ∷
   rw 4 q40 ∷
   rw 7 q33 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q40 ∷
   rw 7 q40 ∷
   rw 10 q33 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q40 ∷
   rw 10 q40 ∷
   rw 13 q33 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q40 ∷
   rw 13 q38 ∷
   rw 10 q46 ∷
   rw 7 q49 ∷
   rw 4 q46 ∷
   rw 21 q33 ∷
   rw 20 q34 ∷
   rw 19 q43 ∷
   rw 18 q36 ∷
   rw 17 q36 ∷
   rw 16 q37 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q38 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   re 12 1 (ℓ "乏久乏") ∷
   rw 14 q38 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q38 ∷
   rw 8 q37 ∷
   rw 9 q52 ∷
   rw⁻ 8 q36 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q34 ∷
   rw 12 q40 ∷
   rw 15 q33 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q40 ∷
   rw 15 q38 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = sE 2024 lem-S2-at0213-ᵖ-1
  q54 : Eqn
  q54 = sE 2063 lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023
  q55 : Eqn
  q55 = sE 2024 lem-S2-at0213-ᵖ-1

-- pass [X3 CSd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞乊丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞乊丞") ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞乊丞中九丮九") (ℓ "中九丮九丞乊丞")
  (rw 3 q53 ∷
   rw 0 q54 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = sE 2061 lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023

-- pass [X3 CKd32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞乘丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞乘丞中九丮九") (ℓ "中九丮九丞乘丞")
  (rw 3 q53 ∷
   rw 0 q56 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 2062 lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023

-- pass [X3 CS32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞义丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞义丞中九丮九") (ℓ "中九丮九丞义丞")
  (rw 3 q53 ∷
   rw 0 q57 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 2077 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2
  q59 : Eqn
  q59 = sE 2078 lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2

-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 6 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (ℓ "乣义乣乊丞乞丞且丨丞乞丞丕丧") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞且丨丞乞丞丕丧乣义乣乊") ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = derive (ℓ "乣义乣乊丞乞丞且丨丞乞丞丕丧") (ℓ "丞乞丞且丨丞乞丞丕丧乣义乣乊")
  (rw 0 q23 ∷
   rw 3 q58 ∷
   rw 4 q25 ∷
   rw 5 q23 ∷
   rw 8 q59 ∷
   rw 9 q24 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 2065 lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023

-- pass [X3 CK32 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞乗丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞乗丞中九丮九") (ℓ "中九丮九丞乗丞")
  (rw 3 q53 ∷
   rw 0 q60 ∷
   rw⁻ 0 q55 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 2085 lem-S2-at2013-ᵖ-1
  q62 : Eqn
  q62 = sE 2064 lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203
  q63 : Eqn
  q63 = sE 2085 lem-S2-at2013-ᵖ-1

-- pass [X3 CK30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞乑丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞乑丞义乣乊乣") (ℓ "义乣乊乣丞乑丞")
  (rw 3 q61 ∷
   rw 0 q62 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = sE 2067 lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203

-- pass [X3 CS30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞中丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞中丞义乣乊乣") (ℓ "义乣乊乣丞中丞")
  (rw 3 q61 ∷
   rw 0 q64 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = sE 2068 lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203

-- pass [X3 CSd30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞丮丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞丮丞义乣乊乣") (ℓ "义乣乊乣丞丮丞")
  (rw 3 q61 ∷
   rw 0 q65 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = sE 2066 lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203

-- pass [X3 CKd30 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞乒丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞乒丞义乣乊乣") (ℓ "义乣乊乣丞乒丞")
  (rw 3 q61 ∷
   rw 0 q66 ∷
   rw⁻ 0 q63 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 5 W
  q68 : Eqn
  q68 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q69 : Eqn
  q69 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q70 : Eqn
  q70 = wE 76 W
  q71 : Eqn
  q71 = wE 29 W
  q72 : Eqn
  q72 = wE 31 W
  q73 : Eqn
  q73 = wE 2102 W
  q74 : Eqn
  q74 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q75 : Eqn
  q75 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q76 : Eqn
  q76 = wE 2103 W

-- pass [X2 CSd20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "丘丨丘丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "丘丨丘丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞丘丨丘")
  (rw 4 q67 ∷
   rw⁻ 3 q68 ∷
   rw⁻ 2 q69 ∷
   rw 1 q70 ∷
   rw⁻ 0 q69 ∷
   rw 1 q6 ∷
   rw 0 q68 ∷
   rw 1 q69 ∷
   rw 2 q71 ∷
   rw 3 q69 ∷
   rw 4 q72 ∷
   rw 1 q73 ∷
   rw 9 q74 ∷
   rw 6 q75 ∷
   rw 3 q74 ∷
   rw 7 q76 ∷
   rw 13 q67 ∷
   rw⁻ 12 q68 ∷
   rw⁻ 11 q69 ∷
   rw 10 q70 ∷
   rw⁻ 9 q69 ∷
   rw 10 q6 ∷
   rw 9 q68 ∷
   rw 10 q69 ∷
   rw 11 q71 ∷
   rw 12 q69 ∷
   rw 13 q72 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 140 W
  q78 : Eqn
  q78 = wE 142 W
  q79 : Eqn
  q79 = wE 2045 W
  q80 : Eqn
  q80 = wE 2046 W

-- pass [X2 CK20 X2] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 29 steps
lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "丘乄丘丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "丘乄丘丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞丘乄丘")
  (rw 4 q67 ∷
   rw⁻ 3 q68 ∷
   rw⁻ 2 q69 ∷
   rw 1 q77 ∷
   rw⁻ 0 q69 ∷
   rw 1 q11 ∷
   rw 0 q68 ∷
   rw 1 q69 ∷
   rw 2 q78 ∷
   rw 3 q69 ∷
   rw 4 q72 ∷
   rw 1 q79 ∷
   rw 15 q75 ∷
   rw 12 q74 ∷
   rw 9 q74 ∷
   rw 6 q75 ∷
   rw 3 q74 ∷
   rw 7 q80 ∷
   rw 13 q67 ∷
   rw⁻ 12 q68 ∷
   rw⁻ 11 q69 ∷
   rw 10 q77 ∷
   rw⁻ 9 q69 ∷
   rw 10 q11 ∷
   rw 9 q68 ∷
   rw 10 q69 ∷
   rw 11 q78 ∷
   rw 12 q69 ∷
   rw 13 q72 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 2083 lem-S2-at1023-ᵖ-1
  q82 : Eqn
  q82 = sE 2072 lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103
  q83 : Eqn
  q83 = sE 2083 lem-S2-at1023-ᵖ-1

-- pass [X3 CSd30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞丮丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞丮丞丽习举习") (ℓ "丽习举习丞丮丞")
  (rw 3 q81 ∷
   rw 0 q82 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = sE 2070 lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103

-- pass [X3 CKd30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞乒丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞乒丞丽习举习") (ℓ "丽习举习丞乒丞")
  (rw 3 q81 ∷
   rw 0 q84 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = sE 2069 lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103

-- pass [X3 CK30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞乑丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞乑丞丽习举习") (ℓ "丽习举习丞乑丞")
  (rw 3 q81 ∷
   rw 0 q85 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = sE 2071 lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103

-- pass [X3 CS30 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞中丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞中丞丽习举习") (ℓ "丽习举习丞中丞")
  (rw 3 q81 ∷
   rw 0 q86 ∷
   rw⁻ 0 q83 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = wE 872 W
  q88 : Eqn
  q88 = wE 2142 W
  q89 : Eqn
  q89 = sE 2058 lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q90 : Eqn
  q90 = wE 388 W
  q91 : Eqn
  q91 = wE 2143 W

-- pass [X1 CKd10 X1] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丒丵丒九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丒丵丒九中九丮") (ℓ "九中九丮丒丵丒")
  (rw 7 q87 ∷
   rw 8 q88 ∷
   rw 9 q87 ∷
   rw⁻ 3 q89 ∷
   rw 2 q90 ∷
   rw 1 q91 ∷
   rw 0 q90 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = sE 1778 lem-S2
  q93 : Eqn
  q93 = sE 2087 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q94 : Eqn
  q94 = sE 1778 lem-S2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "九中九丮丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "九中九丮丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞九中九丮")
  (rw 0 q92 ∷
   rw 0 q93 ∷
   rw⁻ 10 q94 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = sE 2088 lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "中九丮九丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "中九丮九丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞中九丮九")
  (rw⁻ 0 q95 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CK21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘乇丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘乇丘丽习举习") (ℓ "丽习举习丘乇丘")
  (rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q27 ∷
   rw⁻ 4 q96 ∷
   rw 10 q30 ∷
   rw 9 q31 ∷
   rw 8 q32 ∷
   rw 7 q31 ∷ []) Eq.refl

-- resp S0 K0 CS01 TOFF023 CSd01 TOFF023 Kd0 Sd0: 1 steps
lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 : ⟪ (ℓ "丈上丠也両也下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三") ⟫ʷ
lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 = derive (ℓ "丈上丠也両也下三") (ℓ "丈上中九丮九下三")
  (rw⁻ 2 q55 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = sE 2084 lem-S2-at1203-ᵖ-1

-- resp S1 K1 CS01 TOFF123 CSd01 TOFF123 Kd1 Sd1: 1 steps
lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 : ⟪ (ℓ "与丐丠乢両乢丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐丽习举习丑丏") ⟫ʷ
lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 = derive (ℓ "与丐丠乢両乢丑丏") (ℓ "与丐丽习举习丑丏")
  (rw⁻ 2 q97 ∷ []) Eq.refl

-- resp S2 K2 CS12 TOFF203 CSd12 TOFF203 Kd2 Sd2: 1 steps
lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 : ⟪ (ℓ "且世丶乤丷乤丗丕") ⟫ʷ ≈ ⟪ (ℓ "且世义乣乊乣丗丕") ⟫ʷ
lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 = derive (ℓ "且世丶乤丷乤丗丕") (ℓ "且世义乣乊乣丗丕")
  (rw⁻ 2 q63 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = sE 2086 lem-S2-at2103-ᵖ-1

-- resp S2 K2 CS02 TOFF213 CSd02 TOFF213 Kd2 Sd2: 1 steps
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 : ⟪ (ℓ "且世丧乥丨乥丗丕") ⟫ʷ ≈ ⟪ (ℓ "且世义乣乊乣丗丕") ⟫ʷ
lem-resp-S2-K2-CS02-TOFF213-CSd02-TOFF213-Kd2-Sd2 = derive (ℓ "且世丧乥丨乥丗丕") (ℓ "且世义乣乊乣丗丕")
  (rw⁻ 2 q98 ∷ []) Eq.refl

-- resp S1 K1 CS12 TOFF103 CSd12 TOFF103 Kd1 Sd1: 1 steps
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 : ⟪ (ℓ "与丐丶乡丷乡丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐丽习举习丑丏") ⟫ʷ
lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 = derive (ℓ "与丐丶乡丷乡丑丏") (ℓ "与丐丽习举习丑丏")
  (rw⁻ 2 q83 ∷ []) Eq.refl
