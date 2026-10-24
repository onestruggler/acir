{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD625 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D625 (W : Ws) (Sᴰ : SD625) where

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
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 2 Sᴰ
  lem-pass-CS13-vs-Sd0 : St 1428
  lem-pass-CS13-vs-Sd0 = pickᴰ 3 Sᴰ
  lem-pass-S1-vs-CS13 : St 884
  lem-pass-S1-vs-CS13 = pickᴰ 4 Sᴰ
  lem-pass-Sd1-vs-CS13 : St 888
  lem-pass-Sd1-vs-CS13 = pickᴰ 5 Sᴰ
  lem-pass-CS23-vs-CS02 : St 890
  lem-pass-CS23-vs-CS02 = pickᴰ 6 Sᴰ
  lem-pass-CS23-vs-CS03 : St 1442
  lem-pass-CS23-vs-CS03 = pickᴰ 7 Sᴰ
  lem-pass-CS23-vs-CSd02 : St 891
  lem-pass-CS23-vs-CSd02 = pickᴰ 8 Sᴰ
  lem-pass-CS23-vs-CSd03 : St 1443
  lem-pass-CS23-vs-CSd03 = pickᴰ 9 Sᴰ
  lem-pass-CS23-vs-S0 : St 177
  lem-pass-CS23-vs-S0 = pickᴰ 10 Sᴰ
  lem-pass-CS23-vs-Sd0 : St 157
  lem-pass-CS23-vs-Sd0 = pickᴰ 11 Sᴰ
  lem-pass-CS03-vs-CSd23 : St 1466
  lem-pass-CS03-vs-CSd23 = pickᴰ 12 Sᴰ
  lem-pass-CS13-vs-CS01 : St 1467
  lem-pass-CS13-vs-CS01 = pickᴰ 13 Sᴰ
  lem-pass-CS13-vs-CSd01 : St 1468
  lem-pass-CS13-vs-CSd01 = pickᴰ 14 Sᴰ
  lem-pass-CS23-vs-S2 : St 898
  lem-pass-CS23-vs-S2 = pickᴰ 15 Sᴰ
  lem-pass-CS23-vs-S3 : St 1469
  lem-pass-CS23-vs-S3 = pickᴰ 16 Sᴰ
  lem-pass-CS23-vs-Sd2 : St 899
  lem-pass-CS23-vs-Sd2 = pickᴰ 17 Sᴰ
  lem-pass-CS23-vs-Sd3 : St 159
  lem-pass-CS23-vs-Sd3 = pickᴰ 18 Sᴰ
  lem-pass-CS23-vs-iI : St 160
  lem-pass-CS23-vs-iI = pickᴰ 19 Sᴰ
  lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 : St 1470
  lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 = pickᴰ 20 Sᴰ
  lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 : St 1471
  lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 = pickᴰ 21 Sᴰ
  lem-pass-CS13-vs-TOFF012 : St 1434
  lem-pass-CS13-vs-TOFF012 = pickᴰ 22 Sᴰ
  lem-pass-CS03-vs-TOFF201 : St 1472
  lem-pass-CS03-vs-TOFF201 = pickᴰ 23 Sᴰ
  lem-pass-CS13-vs-TOFF023 : St 1473
  lem-pass-CS13-vs-TOFF023 = pickᴰ 24 Sᴰ
  lem-pass-CS23-vs-TOFF012 : St 1459
  lem-pass-CS23-vs-TOFF012 = pickᴰ 25 Sᴰ
  lem-pass-CS23-vs-TOFF013 : St 1460
  lem-pass-CS23-vs-TOFF013 = pickᴰ 26 Sᴰ
  lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : St 1474
  lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 27 Sᴰ
  lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : St 1475
  lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 28 Sᴰ
  lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 : St 1476
  lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 = pickᴰ 29 Sᴰ
  lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : St 1477
  lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = pickᴰ 30 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 121 W
  q4 : Eqn
  q4 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = wE 30 W
  q6 : Eqn
  q6 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 122 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 127 W
  q12 : Eqn
  q12 = wE 118 W
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 74 W
  q15 : Eqn
  q15 = wE 125 W
  q16 : Eqn
  q16 = wE 1373 W
  q17 : Eqn
  q17 = wE 39 W
  q18 : Eqn
  q18 = wE 123 W
  q19 : Eqn
  q19 = wE 24 W
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W
  q22 : Eqn
  q22 = wE 65 W
  q23 : Eqn
  q23 = eqn (ℓ "丳义") (ℓ "义丳") (low-comm (CX₁₀) (CS))
  q24 : Eqn
  q24 = wE 48 W
  q25 : Eqn
  q25 = sE 1473 lem-pass-CS13-vs-TOFF023
  q26 : Eqn
  q26 = wE 6 W
  q27 : Eqn
  q27 = wE 1375 W
  q28 : Eqn
  q28 = sE 884 lem-pass-S1-vs-CS13
  q29 : Eqn
  q29 = sE 1468 lem-pass-CS13-vs-CSd01
  q30 : Eqn
  q30 = sE 888 lem-pass-Sd1-vs-CS13
  q31 : Eqn
  q31 = sE 1467 lem-pass-CS13-vs-CS01

-- pass [CS13] [X3 TOFF023 X3 S1 CSd01 X3 TOFF023 X3 Sd1 CS01]: 272 steps
lem-pass-CS13-vs-X3-TOFF023-X3-S1-CSd01-X3-TOFF023-X3-Sd1-CS01 : ⟪ (ℓ "丽丞也丞与両丞也丞丏丠") ⟫ʷ ≈ ⟪ (ℓ "丞也丞与両丞也丞丏丠丽") ⟫ʷ
lem-pass-CS13-vs-X3-TOFF023-X3-S1-CSd01-X3-TOFF023-X3-Sd1-CS01 = derive (ℓ "丽丞也丞与両丞也丞丏丠") (ℓ "丞也丞与両丞也丞丏丠丽")
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   re 2 1 (ℓ "並乢並") ∷
   re 3 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q7 ∷
   rw 8 q13 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (ℓ "丽") ∷
   rw 6 q14 ∷
   rw⁻ 5 q6 ∷
   rw 4 q14 ∷
   rw⁻ 3 q4 ∷
   rw 2 q12 ∷
   rw 3 q15 ∷
   re 3 8 (ℓ "乢") ∷
   rw⁻ 1 q2 ∷
   rw 2 q16 ∷
   rw 1 q17 ∷
   re 3 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 2 q1 ∷
   rw 3 q18 ∷
   rw 4 q4 ∷
   rw 5 q19 ∷
   rw 6 q6 ∷
   rw 7 q19 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q7 ∷
   rw 9 q20 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q18 ∷
   rw 10 q21 ∷
   rw 3 q15 ∷
   re 3 8 (ℓ "乢") ∷
   re 2 3 (ℓ "也") ∷
   rw 3 q10 ∷
   re 1 1 (ℓ "丼丳丼") ∷
   rw 0 q22 ∷
   rw⁻ 1 q23 ∷
   rw 2 q24 ∷
   re 0 3 (ℓ "乃") ∷
   rw 1 q25 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 9 q10 ∷
   rw 8 q11 ∷
   rw 7 q12 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q7 ∷
   rw 7 q13 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q14 ∷
   rw⁻ 4 q6 ∷
   rw 3 q14 ∷
   rw⁻ 2 q4 ∷
   rw 1 q12 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乢") ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q18 ∷
   rw 3 q4 ∷
   rw 4 q19 ∷
   rw 5 q6 ∷
   rw 6 q19 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q20 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q18 ∷
   rw 9 q21 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw⁻ 3 q28 ∷
   rw 4 q29 ∷
   rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (ℓ "並乢並") ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q5 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q7 ∷
   rw 13 q8 ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q7 ∷
   rw 13 q13 ∷
   rw⁻ 12 q7 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q14 ∷
   rw⁻ 10 q6 ∷
   rw 9 q14 ∷
   rw⁻ 8 q4 ∷
   rw 7 q12 ∷
   rw 8 q15 ∷
   re 8 8 (ℓ "乢") ∷
   rw⁻ 6 q2 ∷
   rw 7 q16 ∷
   rw 6 q17 ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q5 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q7 ∷
   rw 13 q8 ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 7 q1 ∷
   rw 8 q18 ∷
   rw 9 q4 ∷
   rw 10 q19 ∷
   rw 11 q6 ∷
   rw 12 q19 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q7 ∷
   rw 14 q20 ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "丽") ∷
   rw 14 q18 ∷
   rw 15 q21 ∷
   rw 8 q15 ∷
   re 8 8 (ℓ "乢") ∷
   re 7 3 (ℓ "也") ∷
   rw 8 q10 ∷
   re 6 1 (ℓ "丼丳丼") ∷
   rw 5 q22 ∷
   rw⁻ 6 q23 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "乃") ∷
   rw 6 q25 ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "並乢並") ∷
   re 7 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   rw 12 q12 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q7 ∷
   rw 12 q13 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (ℓ "丽") ∷
   rw 10 q14 ∷
   rw⁻ 9 q6 ∷
   rw 8 q14 ∷
   rw⁻ 7 q4 ∷
   rw 6 q12 ∷
   rw 7 q15 ∷
   re 7 8 (ℓ "乢") ∷
   rw 5 q26 ∷
   rw 6 q27 ∷
   rw 5 q2 ∷
   re 7 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 6 q1 ∷
   rw 7 q18 ∷
   rw 8 q4 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q7 ∷
   rw 13 q20 ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "丽") ∷
   rw 13 q18 ∷
   rw 14 q21 ∷
   rw 7 q15 ∷
   re 7 8 (ℓ "乢") ∷
   re 6 3 (ℓ "也") ∷
   rw 7 q2 ∷
   rw 8 q10 ∷
   rw⁻ 8 q30 ∷
   rw 9 q31 ∷ []) Eq.refl

-- pass [CS13] [X3 TOFF023 X3]: 134 steps
lem-pass-CS13-vs-X3-TOFF023-X3 : ⟪ (ℓ "丽丞也丞") ⟫ʷ ≈ ⟪ (ℓ "丞也丞丽") ⟫ʷ
lem-pass-CS13-vs-X3-TOFF023-X3 = derive (ℓ "丽丞也丞") (ℓ "丞也丞丽")
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   re 2 1 (ℓ "並乢並") ∷
   re 3 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q7 ∷
   rw 8 q13 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (ℓ "丽") ∷
   rw 6 q14 ∷
   rw⁻ 5 q6 ∷
   rw 4 q14 ∷
   rw⁻ 3 q4 ∷
   rw 2 q12 ∷
   rw 3 q15 ∷
   re 3 8 (ℓ "乢") ∷
   rw⁻ 1 q2 ∷
   rw 2 q16 ∷
   rw 1 q17 ∷
   re 3 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 2 q1 ∷
   rw 3 q18 ∷
   rw 4 q4 ∷
   rw 5 q19 ∷
   rw 6 q6 ∷
   rw 7 q19 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q7 ∷
   rw 9 q20 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q18 ∷
   rw 10 q21 ∷
   rw 3 q15 ∷
   re 3 8 (ℓ "乢") ∷
   re 2 3 (ℓ "也") ∷
   rw 3 q10 ∷
   re 1 1 (ℓ "丼丳丼") ∷
   rw 0 q22 ∷
   rw⁻ 1 q23 ∷
   rw 2 q24 ∷
   re 0 3 (ℓ "乃") ∷
   rw 1 q25 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 9 q10 ∷
   rw 8 q11 ∷
   rw 7 q12 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q7 ∷
   rw 7 q13 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q14 ∷
   rw⁻ 4 q6 ∷
   rw 3 q14 ∷
   rw⁻ 2 q4 ∷
   rw 1 q12 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乢") ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q18 ∷
   rw 3 q4 ∷
   rw 4 q19 ∷
   rw 5 q6 ∷
   rw 6 q19 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q20 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q18 ∷
   rw 9 q21 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   rw 2 q2 ∷
   rw 3 q10 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q33 : Eqn
  q33 = wE 1674 W
  q34 : Eqn
  q34 = sE 1477 lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0
  q35 : Eqn
  q35 = wE 1675 W

-- pass [CKd32] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 5 steps
lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "乘丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞乘") ⟫ʷ
lem-pass-CKd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "乘丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞乘")
  (rw 1 q32 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 7 q35 ∷
   rw⁻ 0 q32 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 160 lem-pass-CS23-vs-iI
  q37 : Eqn
  q37 = sE 157 lem-pass-CS23-vs-Sd0
  q38 : Eqn
  q38 = sE 159 lem-pass-CS23-vs-Sd3
  q39 : Eqn
  q39 = sE 1442 lem-pass-CS23-vs-CS03
  q40 : Eqn
  q40 = sE 1459 lem-pass-CS23-vs-TOFF012
  q41 : Eqn
  q41 = sE 177 lem-pass-CS23-vs-S0
  q42 : Eqn
  q42 = sE 1469 lem-pass-CS23-vs-S3
  q43 : Eqn
  q43 = sE 1443 lem-pass-CS23-vs-CSd03

-- pass [CS23] [iI Sd0 Sd3 CS03 TOFF012 iI iI iI S0 S3 CSd03 TOFF012]: 12 steps
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03-TOFF012 : ⟪ (ℓ "义一三丛中九一一一丈业丮九") ⟫ʷ ≈ ⟪ (ℓ "一三丛中九一一一丈业丮九义") ⟫ʷ
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03-TOFF012 = derive (ℓ "义一三丛中九一一一丈业丮九") (ℓ "一三丛中九一一一丈业丮九义")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 2 q38 ∷
   rw 3 q39 ∷
   rw 4 q40 ∷
   rw 5 q36 ∷
   rw 6 q36 ∷
   rw 7 q36 ∷
   rw 8 q41 ∷
   rw 9 q42 ∷
   rw 10 q43 ∷
   rw 11 q40 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 1442 lem-pass-CS23-vs-CS03
  q45 : Eqn
  q45 = sE 1472 lem-pass-CS03-vs-TOFF201
  q46 : Eqn
  q46 = sE 1466 lem-pass-CS03-vs-CSd23

-- pass [CS03] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "中义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣中") ⟫ʷ
lem-pass-CS03-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "中义乣乊乣") (ℓ "义乣乊乣中")
  (rw⁻ 0 q44 ∷
   rw 1 q45 ∷
   rw 2 q46 ∷
   rw 3 q45 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = sE 1476 lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03
  q48 : Eqn
  q48 = sE 1471 lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03
  q49 : Eqn
  q49 = sE 1470 lem-pass-CS23-vs-iI-Sd0-Sd3-CS03

-- pass [CS23 TOFF201 CSd23 TOFF201] [iI Sd0 Sd3 CS03]: 4 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 : ⟪ (ℓ "义乣乊乣一三丛中") ⟫ʷ ≈ ⟪ (ℓ "一三丛中义乣乊乣") ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI-Sd0-Sd3-CS03 = derive (ℓ "义乣乊乣一三丛中") (ℓ "一三丛中义乣乊乣")
  (rw 3 q47 ∷
   rw 2 q48 ∷
   rw 1 q47 ∷
   rw 0 q49 ∷ []) Eq.refl

-- pass [CS23] [TOFF012 iI Sd0 Sd3 CS03 TOFF012 iI iI iI S0 S3 CSd03]: 12 steps
lem-pass-CS23-vs-TOFF012-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03 : ⟪ (ℓ "义九一三丛中九一一一丈业丮") ⟫ʷ ≈ ⟪ (ℓ "九一三丛中九一一一丈业丮义") ⟫ʷ
lem-pass-CS23-vs-TOFF012-iI-Sd0-Sd3-CS03-TOFF012-iI-iI-iI-S0-S3-CSd03 = derive (ℓ "义九一三丛中九一一一丈业丮") (ℓ "九一三丛中九一一一丈业丮义")
  (rw 0 q40 ∷
   rw 1 q36 ∷
   rw 2 q37 ∷
   rw 3 q38 ∷
   rw 4 q39 ∷
   rw 5 q40 ∷
   rw 6 q36 ∷
   rw 7 q36 ∷
   rw 8 q36 ∷
   rw 9 q41 ∷
   rw 10 q42 ∷
   rw 11 q43 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 1 W
  q51 : Eqn
  q51 = wE 173 W
  q52 : Eqn
  q52 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q53 : Eqn
  q53 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q54 : Eqn
  q54 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q55 : Eqn
  q55 = wE 3 W
  q56 : Eqn
  q56 = wE 56 W
  q57 : Eqn
  q57 = wE 1362 W
  q58 : Eqn
  q58 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q59 : Eqn
  q59 = sE 1460 lem-pass-CS23-vs-TOFF013
  q60 : Eqn
  q60 = wE 1364 W
  q61 : Eqn
  q61 = wE 175 W
  q62 : Eqn
  q62 = sE 898 lem-pass-CS23-vs-S2
  q63 : Eqn
  q63 = sE 891 lem-pass-CS23-vs-CSd02
  q64 : Eqn
  q64 = sE 899 lem-pass-CS23-vs-Sd2
  q65 : Eqn
  q65 = sE 890 lem-pass-CS23-vs-CS02

-- pass [CS23] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 248 steps
lem-pass-CS23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (ℓ "义丞乞丞且丨丞乞丞丕丧") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞且丨丞乞丞丕丧义") ⟫ʷ
lem-pass-CS23-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = derive (ℓ "义丞乞丞且丨丞乞丞丕丧") (ℓ "丞乞丞且丨丞乞丞丕丧义")
  (rw 4 q50 ∷
   rw 3 q51 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q52 ∷
   rw 5 q50 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q53 ∷
   rw 7 q50 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q53 ∷
   rw 9 q50 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q52 ∷
   rw⁻ 9 q54 ∷
   rw 10 q55 ∷
   rw 9 q54 ∷
   rw 8 q52 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q55 ∷
   rw 6 q53 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q55 ∷
   rw 4 q53 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q55 ∷
   rw 2 q52 ∷
   rw 3 q56 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q51 ∷
   rw 2 q57 ∷
   rw⁻ 1 q58 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q52 ∷
   rw 5 q50 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q53 ∷
   rw 7 q50 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q53 ∷
   rw 9 q50 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q52 ∷
   rw⁻ 9 q54 ∷
   rw 2 q50 ∷
   rw⁻ 3 q52 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q55 ∷
   rw⁻ 5 q53 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q55 ∷
   rw⁻ 7 q53 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q55 ∷
   rw⁻ 9 q52 ∷
   rw⁻ 10 q54 ∷
   rw 3 q56 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q55 ∷
   rw⁻ 0 q23 ∷
   rw 1 q59 ∷
   rw 2 q50 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q52 ∷
   rw 4 q50 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q53 ∷
   rw 6 q50 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q53 ∷
   rw 8 q50 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q52 ∷
   rw⁻ 8 q54 ∷
   rw 9 q55 ∷
   rw 8 q54 ∷
   rw 7 q52 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q55 ∷
   rw 5 q53 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q55 ∷
   rw 3 q53 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q55 ∷
   rw 1 q52 ∷
   rw 2 q56 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q58 ∷
   rw 1 q60 ∷
   rw 0 q61 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q52 ∷
   rw 4 q50 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q53 ∷
   rw 6 q50 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q53 ∷
   rw 8 q50 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q52 ∷
   rw⁻ 8 q54 ∷
   rw 1 q50 ∷
   rw⁻ 2 q52 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q55 ∷
   rw⁻ 4 q53 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q55 ∷
   rw⁻ 6 q53 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q55 ∷
   rw⁻ 8 q52 ∷
   rw⁻ 9 q54 ∷
   rw 2 q56 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q61 ∷
   rw 3 q55 ∷
   rw 3 q62 ∷
   rw 4 q63 ∷
   rw 9 q50 ∷
   rw 8 q51 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q52 ∷
   rw 10 q50 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q53 ∷
   rw 12 q50 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q53 ∷
   rw 14 q50 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q52 ∷
   rw⁻ 14 q54 ∷
   rw 15 q55 ∷
   rw 14 q54 ∷
   rw 13 q52 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q55 ∷
   rw 11 q53 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q55 ∷
   rw 9 q53 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q55 ∷
   rw 7 q52 ∷
   rw 8 q56 ∷
   re 8 8 (ℓ "九") ∷
   rw 6 q51 ∷
   rw 7 q57 ∷
   rw⁻ 6 q58 ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q52 ∷
   rw 10 q50 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q53 ∷
   rw 12 q50 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q53 ∷
   rw 14 q50 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q52 ∷
   rw⁻ 14 q54 ∷
   rw 7 q50 ∷
   rw⁻ 8 q52 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q55 ∷
   rw⁻ 10 q53 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q55 ∷
   rw⁻ 12 q53 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q55 ∷
   rw⁻ 14 q52 ∷
   rw⁻ 15 q54 ∷
   rw 8 q56 ∷
   re 8 8 (ℓ "九") ∷
   re 7 3 (ℓ "乞") ∷
   rw 8 q55 ∷
   rw⁻ 5 q23 ∷
   rw 6 q59 ∷
   rw 7 q50 ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q52 ∷
   rw 9 q50 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q53 ∷
   rw 11 q50 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q53 ∷
   rw 13 q50 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q52 ∷
   rw⁻ 13 q54 ∷
   rw 14 q55 ∷
   rw 13 q54 ∷
   rw 12 q52 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q55 ∷
   rw 10 q53 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q55 ∷
   rw 8 q53 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q55 ∷
   rw 6 q52 ∷
   rw 7 q56 ∷
   re 7 8 (ℓ "九") ∷
   rw 5 q58 ∷
   rw 6 q60 ∷
   rw 5 q61 ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q52 ∷
   rw 9 q50 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q53 ∷
   rw 11 q50 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q53 ∷
   rw 13 q50 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q52 ∷
   rw⁻ 13 q54 ∷
   rw 6 q50 ∷
   rw⁻ 7 q52 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q55 ∷
   rw⁻ 9 q53 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q55 ∷
   rw⁻ 11 q53 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q55 ∷
   rw⁻ 13 q52 ∷
   rw⁻ 14 q54 ∷
   rw 7 q56 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw 7 q61 ∷
   rw 8 q55 ∷
   rw 8 q64 ∷
   rw 9 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = sE 63 lem-pass-CS13-vs-S0
  q67 : Eqn
  q67 = sE 1093 lem-pass-CS13-vs-CSd03
  q68 : Eqn
  q68 = sE 1434 lem-pass-CS13-vs-TOFF012
  q69 : Eqn
  q69 = sE 1428 lem-pass-CS13-vs-Sd0
  q70 : Eqn
  q70 = sE 1092 lem-pass-CS13-vs-CS03

-- pass [CS13] [S0 CSd03 TOFF012 Sd0 CS03 TOFF012]: 6 steps
lem-pass-CS13-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 : ⟪ (ℓ "丽丈丮九三中九") ⟫ʷ ≈ ⟪ (ℓ "丈丮九三中九丽") ⟫ʷ
lem-pass-CS13-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 = derive (ℓ "丽丈丮九三中九") (ℓ "丈丮九三中九丽")
  (rw 0 q66 ∷
   rw 1 q67 ∷
   rw 2 q68 ∷
   rw 3 q69 ∷
   rw 4 q70 ∷
   rw 5 q68 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = sE 1474 lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [CSd03]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CSd03 : ⟪ (ℓ "丽习举习丮") ⟫ʷ ≈ ⟪ (ℓ "丮丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CSd03 = derive (ℓ "丽习举习丮") (ℓ "丮丽习举习")
  (rw⁻ 0 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = sE 1475 lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [S0 CSd03]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 : ⟪ (ℓ "丽习举习丈丮") ⟫ʷ ≈ ⟪ (ℓ "丈丮丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03 = derive (ℓ "丽习举习丈丮") (ℓ "丈丮丽习举习")
  (rw⁻ 0 q72 ∷ []) Eq.refl

-- pass [CS13] [TOFF012 S0 CSd03 TOFF012 Sd0 CS03]: 6 steps
lem-pass-CS13-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 : ⟪ (ℓ "丽九丈丮九三中") ⟫ʷ ≈ ⟪ (ℓ "九丈丮九三中丽") ⟫ʷ
lem-pass-CS13-vs-TOFF012-S0-CSd03-TOFF012-Sd0-CS03 = derive (ℓ "丽九丈丮九三中") (ℓ "九丈丮九三中丽")
  (rw 0 q68 ∷
   rw 1 q66 ∷
   rw 2 q67 ∷
   rw 3 q68 ∷
   rw 4 q69 ∷
   rw 5 q70 ∷ []) Eq.refl
