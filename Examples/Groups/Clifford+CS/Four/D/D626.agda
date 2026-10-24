{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD626 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D626 (W : Ws) (Sᴰ : SD626) where

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
  lem-pass-CS23-vs-CS03 : St 1442
  lem-pass-CS23-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CS23-vs-CSd03 : St 1443
  lem-pass-CS23-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS23-vs-S0 : St 177
  lem-pass-CS23-vs-S0 = pickᴰ 2 Sᴰ
  lem-pass-CS23-vs-Sd0 : St 157
  lem-pass-CS23-vs-Sd0 = pickᴰ 3 Sᴰ
  lem-pass-CS13-vs-CS01 : St 1467
  lem-pass-CS13-vs-CS01 = pickᴰ 4 Sᴰ
  lem-pass-CS13-vs-CSd01 : St 1468
  lem-pass-CS13-vs-CSd01 = pickᴰ 5 Sᴰ
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3 : St 1478
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 6 Sᴰ
  lem-pass-CSd03-vs-CSd23 : St 1479
  lem-pass-CSd03-vs-CSd23 = pickᴰ 7 Sᴰ
  lem-pass-CSd03-vs-X1-X3-TOFF013-X1-X3 : St 1480
  lem-pass-CSd03-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 8 Sᴰ
  lem-pass-S0-vs-CSd23 : St 179
  lem-pass-S0-vs-CSd23 = pickᴰ 9 Sᴰ
  lem-pass-CS13-vs-TOFF012 : St 1434
  lem-pass-CS13-vs-TOFF012 = pickᴰ 10 Sᴰ
  lem-pass-CSd13-vs-TOFF012 : St 1436
  lem-pass-CSd13-vs-TOFF012 = pickᴰ 11 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-III-units-2 : St 1481
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-III-units-2 = pickᴰ 12 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-III-units-1 : St 1482
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-III-units-1 = pickᴰ 13 Sᴰ
  lem-pass-CS13-vs-TOFF023 : St 1473
  lem-pass-CS13-vs-TOFF023 = pickᴰ 14 Sᴰ
  lem-pass-CS23-vs-TOFF012 : St 1459
  lem-pass-CS23-vs-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-CSd03-vs-TOFF201 : St 1483
  lem-pass-CSd03-vs-TOFF201 = pickᴰ 16 Sᴰ
  lem-pass-TOFF012-vs-X1-X3-TOFF013-X1-X3 : St 1484
  lem-pass-TOFF012-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 17 Sᴰ
  lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1485
  lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 18 Sᴰ
  lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1486
  lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 19 Sᴰ
  lem-pass-X2-CS21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 1487
  lem-pass-X2-CS21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 20 Sᴰ
  lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 1488
  lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 21 Sᴰ
  lem-pass-X2-CSd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 1489
  lem-pass-X2-CSd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 22 Sᴰ
  lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : St 1490
  lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = pickᴰ 23 Sᴰ

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
  q28 = sE 1467 lem-pass-CS13-vs-CS01
  q29 : Eqn
  q29 = sE 1468 lem-pass-CS13-vs-CSd01

-- pass [CS13] [X3 TOFF023 X3 CS01 X3 TOFF023 X3 CSd01]: 270 steps
lem-pass-CS13-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 : ⟪ (ℓ "丽丞也丞丠丞也丞両") ⟫ʷ ≈ ⟪ (ℓ "丞也丞丠丞也丞両丽") ⟫ʷ
lem-pass-CS13-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 = derive (ℓ "丽丞也丞丠丞也丞両") (ℓ "丞也丞丠丞也丞両丽")
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
   rw 3 q28 ∷
   rw 8 q1 ∷
   rw⁻ 7 q2 ∷
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
   rw⁻ 5 q2 ∷
   rw 6 q16 ∷
   rw 5 q17 ∷
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
   rw 7 q10 ∷
   re 5 1 (ℓ "丼丳丼") ∷
   rw 4 q22 ∷
   rw⁻ 5 q23 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "乃") ∷
   rw 5 q25 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "並乢並") ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   rw 11 q12 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q7 ∷
   rw 11 q13 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (ℓ "丽") ∷
   rw 9 q14 ∷
   rw⁻ 8 q6 ∷
   rw 7 q14 ∷
   rw⁻ 6 q4 ∷
   rw 5 q12 ∷
   rw 6 q15 ∷
   re 6 8 (ℓ "乢") ∷
   rw 4 q26 ∷
   rw 5 q27 ∷
   rw 4 q2 ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 5 q1 ∷
   rw 6 q18 ∷
   rw 7 q4 ∷
   rw 8 q19 ∷
   rw 9 q6 ∷
   rw 10 q19 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q7 ∷
   rw 12 q20 ∷
   rw 13 q7 ∷
   re 11 3 (ℓ "丽") ∷
   rw 12 q18 ∷
   rw 13 q21 ∷
   rw 6 q15 ∷
   re 6 8 (ℓ "乢") ∷
   re 5 3 (ℓ "也") ∷
   rw 6 q2 ∷
   rw 7 q10 ∷
   rw 7 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 1474 W
  q31 : Eqn
  q31 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q32 : Eqn
  q32 = sE 1488 lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q33 : Eqn
  q33 = wE 1475 W

-- pass [CS21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (ℓ "丶丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丽习举习丘丞丶") ⟫ʷ
lem-pass-CS21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (ℓ "丶丘丞丽习举习丘丞") (ℓ "丘丞丽习举习丘丞丶")
  (rw 0 q30 ∷
   rw 9 q31 ∷
   rw 1 q32 ∷
   rw 7 q33 ∷
   rw⁻ 6 q31 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1480 W
  q35 : Eqn
  q35 = sE 1490 lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3
  q36 : Eqn
  q36 = wE 1481 W

-- pass [CSd21] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 5 steps
lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (ℓ "丷丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丽习举习丘丞丷") ⟫ʷ
lem-pass-CSd21-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (ℓ "丷丘丞丽习举习丘丞") (ℓ "丘丞丽习举习丘丞丷")
  (rw 0 q34 ∷
   rw 9 q31 ∷
   rw 1 q35 ∷
   rw 7 q36 ∷
   rw⁻ 6 q31 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1714 W
  q38 : Eqn
  q38 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q39 : Eqn
  q39 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q40 : Eqn
  q40 = sE 1485 lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q41 : Eqn
  q41 = wE 1715 W

-- pass [CS10] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "丠丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞丠") ⟫ʷ
lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "丠丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞丠")
  (rw 0 q37 ∷
   rw 10 q38 ∷
   rw 11 q39 ∷
   rw 1 q40 ∷
   rw 9 q41 ∷
   rw⁻ 8 q39 ∷
   rw⁻ 7 q38 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 1821 W
  q43 : Eqn
  q43 = sE 1486 lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q44 : Eqn
  q44 = wE 1822 W

-- pass [CSd10] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "両丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞両") ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "両丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞両")
  (rw 0 q42 ∷
   rw 10 q38 ∷
   rw 11 q39 ∷
   rw 1 q43 ∷
   rw 9 q44 ∷
   rw⁻ 8 q39 ∷
   rw⁻ 7 q38 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 1484 lem-pass-TOFF012-vs-X1-X3-TOFF013-X1-X3
  q46 : Eqn
  q46 = sE 1480 lem-pass-CSd03-vs-X1-X3-TOFF013-X1-X3
  q47 : Eqn
  q47 = sE 1478 lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3

-- pass [CS03 TOFF012 CSd03 TOFF012] [X1 X3 TOFF013 X1 X3]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3 : ⟪ (ℓ "中九丮九丒丞乞丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3 = derive (ℓ "中九丮九丒丞乞丒丞") (ℓ "丒丞乞丒丞中九丮九")
  (rw 3 q45 ∷
   rw 2 q46 ∷
   rw 1 q45 ∷
   rw 0 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = sE 177 lem-pass-CS23-vs-S0
  q49 : Eqn
  q49 = sE 1443 lem-pass-CS23-vs-CSd03
  q50 : Eqn
  q50 = sE 1459 lem-pass-CS23-vs-TOFF012
  q51 : Eqn
  q51 = sE 157 lem-pass-CS23-vs-Sd0
  q52 : Eqn
  q52 = sE 1442 lem-pass-CS23-vs-CS03

-- pass [CS23] [S0 CSd03 TOFF012 Sd0 CS03 TOFF012]: 6 steps
lem-pass-CS23-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 : ⟪ (ℓ "义丈丮九三中九") ⟫ʷ ≈ ⟪ (ℓ "丈丮九三中九义") ⟫ʷ
lem-pass-CS23-vs-S0-CSd03-TOFF012-Sd0-CS03-TOFF012 = derive (ℓ "义丈丮九三中九") (ℓ "丈丮九三中九义")
  (rw 0 q48 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   rw 3 q51 ∷
   rw 4 q52 ∷
   rw 5 q50 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = sE 1443 lem-pass-CS23-vs-CSd03
  q54 : Eqn
  q54 = sE 1483 lem-pass-CSd03-vs-TOFF201
  q55 : Eqn
  q55 = sE 1479 lem-pass-CSd03-vs-CSd23

-- pass [CSd03] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丮义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丮") ⟫ʷ
lem-pass-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丮义乣乊乣") (ℓ "义乣乊乣丮")
  (rw⁻ 0 q53 ∷
   rw 1 q54 ∷
   rw 2 q55 ∷
   rw 3 q54 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = sE 177 lem-pass-CS23-vs-S0
  q57 : Eqn
  q57 = wE 1388 W
  q58 : Eqn
  q58 = sE 179 lem-pass-S0-vs-CSd23

-- pass [S0 CSd03] [CS23 TOFF201 CSd23 TOFF201]: 8 steps
lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丈丮义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丈丮") ⟫ʷ
lem-pass-S0-CSd03-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丈丮义乣乊乣") (ℓ "义乣乊乣丈丮")
  (rw⁻ 1 q53 ∷
   rw⁻ 0 q56 ∷
   rw 2 q54 ∷
   rw 1 q57 ∷
   rw 3 q55 ∷
   rw 2 q58 ∷
   rw 4 q54 ∷
   rw 3 q57 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q60 : Eqn
  q60 = sE 1487 lem-pass-X2-CS21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3

-- pass [CS21] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CS21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "丶丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞丶") ⟫ʷ
lem-pass-CS21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "丶丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞丶")
  (rw 1 q59 ∷
   rw 0 q30 ∷
   rw 11 q31 ∷
   rw 1 q60 ∷
   rw 9 q33 ∷
   rw⁻ 0 q59 ∷
   rw⁻ 8 q31 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 1489 lem-pass-X2-CSd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3

-- pass [CSd21] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CSd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "丷丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞丷") ⟫ʷ
lem-pass-CSd21-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "丷丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞丷")
  (rw 1 q59 ∷
   rw 0 q34 ∷
   rw 11 q31 ∷
   rw 1 q61 ∷
   rw 9 q36 ∷
   rw⁻ 0 q59 ∷
   rw⁻ 8 q31 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 1362 W
  q63 : Eqn
  q63 = wE 1 W
  q64 : Eqn
  q64 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q65 : Eqn
  q65 = wE 3 W
  q66 : Eqn
  q66 = wE 1382 W
  q67 : Eqn
  q67 = sE 1434 lem-pass-CS13-vs-TOFF012
  q68 : Eqn
  q68 = wE 1364 W

-- pass [CS13] [X2 TOFF012 X2]: 12 steps
lem-pass-CS13-vs-X2-TOFF012-X2 : ⟪ (ℓ "丽丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丽") ⟫ʷ
lem-pass-CS13-vs-X2-TOFF012-X2 = derive (ℓ "丽丘九丘") (ℓ "丘九丘丽")
  (rw 1 q62 ∷
   rw 2 q63 ∷
   rw 1 q64 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q65 ∷
   rw 1 q66 ∷
   rw⁻ 0 q64 ∷
   rw 3 q63 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q65 ∷
   rw 1 q67 ∷
   rw 0 q68 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 1881 W
  q70 : Eqn
  q70 = sE 1436 lem-pass-CSd13-vs-TOFF012

-- pass [CSd13] [X2 TOFF012 X2]: 12 steps
lem-pass-CSd13-vs-X2-TOFF012-X2 : ⟪ (ℓ "举丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘举") ⟫ʷ
lem-pass-CSd13-vs-X2-TOFF012-X2 = derive (ℓ "举丘九丘") (ℓ "丘九丘举")
  (rw 1 q62 ∷
   rw 2 q63 ∷
   rw 1 q64 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q65 ∷
   rw 1 q69 ∷
   rw⁻ 0 q64 ∷
   rw 3 q63 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q65 ∷
   rw 1 q70 ∷
   rw 0 q68 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 173 W
  q72 : Eqn
  q72 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q73 : Eqn
  q73 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q74 : Eqn
  q74 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q75 : Eqn
  q75 = wE 196 W
  q76 : Eqn
  q76 = wE 1884 W
  q77 : Eqn
  q77 = wE 175 W
  q78 : Eqn
  q78 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q79 : Eqn
  q79 = wE 56 W
  q80 : Eqn
  q80 = sE 1482 lem-Bar⟨SSKSKK32-⟶0⟩-passes-III-units-1
  q81 : Eqn
  q81 = wE 1885 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF103 X3]: 155 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乡丞") (ℓ "丞乡丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 32 q63 ∷
   rw 31 q71 ∷
   re 30 1 (ℓ "乏习乏") ∷
   re 31 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 30 q72 ∷
   rw 33 q63 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q73 ∷
   rw 35 q63 ∷
   re 33 3 (ℓ "举") ∷
   rw⁻ 34 q73 ∷
   rw 37 q63 ∷
   re 35 3 (ℓ "中") ∷
   rw⁻ 36 q72 ∷
   rw⁻ 37 q74 ∷
   rw 38 q65 ∷
   rw 37 q74 ∷
   rw 36 q72 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q65 ∷
   rw 34 q73 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 35 q65 ∷
   rw 32 q73 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q65 ∷
   rw 30 q72 ∷
   rw 31 q75 ∷
   re 31 8 (ℓ "习") ∷
   rw 29 q71 ∷
   rw 30 q76 ∷
   rw 29 q77 ∷
   rw 32 q63 ∷
   re 30 3 (ℓ "乔") ∷
   rw 31 q77 ∷
   rw 32 q77 ∷
   rw 35 q63 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q77 ∷
   rw 35 q77 ∷
   re 37 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 36 q78 ∷
   rw 39 q63 ∷
   re 37 3 (ℓ "丽") ∷
   rw⁻ 38 q73 ∷
   rw 41 q63 ∷
   re 39 3 (ℓ "举") ∷
   rw⁻ 40 q73 ∷
   rw 43 q63 ∷
   re 41 3 (ℓ "中") ∷
   rw⁻ 42 q78 ∷
   rw⁻ 43 q74 ∷
   rw 36 q63 ∷
   rw⁻ 37 q78 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q65 ∷
   rw⁻ 39 q73 ∷
   re 41 1 (ℓ "乏丷乏") ∷
   rw 40 q65 ∷
   rw⁻ 41 q73 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q65 ∷
   rw⁻ 43 q78 ∷
   rw⁻ 44 q74 ∷
   rw 37 q79 ∷
   re 37 8 (ℓ "九") ∷
   re 36 3 (ℓ "乞") ∷
   rw 37 q77 ∷
   rw 38 q77 ∷
   rw 41 q63 ∷
   re 39 3 (ℓ "乒") ∷
   rw 40 q77 ∷
   rw 41 q77 ∷
   rw 44 q63 ∷
   re 42 3 (ℓ "乕") ∷
   rw 43 q77 ∷
   rw 44 q65 ∷
   rw 0 q80 ∷
   rw 15 q63 ∷
   rw 14 q71 ∷
   re 13 1 (ℓ "乏么乏") ∷
   rw 15 q65 ∷
   rw 12 q71 ∷
   rw 11 q71 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q65 ∷
   rw 9 q71 ∷
   rw 8 q71 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q78 ∷
   rw 10 q63 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q73 ∷
   rw 12 q63 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q73 ∷
   rw 14 q63 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q78 ∷
   rw⁻ 14 q74 ∷
   rw 15 q65 ∷
   rw 14 q74 ∷
   rw 13 q78 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q65 ∷
   rw 11 q73 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q65 ∷
   rw 9 q73 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q65 ∷
   rw 7 q78 ∷
   rw 8 q79 ∷
   re 8 8 (ℓ "九") ∷
   rw 6 q71 ∷
   rw 5 q71 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q65 ∷
   rw 3 q71 ∷
   rw 2 q71 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q65 ∷
   rw 0 q71 ∷
   rw 1 q81 ∷
   rw 0 q77 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q72 ∷
   rw 4 q63 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q73 ∷
   rw 6 q63 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q73 ∷
   rw 8 q63 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q72 ∷
   rw⁻ 8 q74 ∷
   rw 1 q63 ∷
   rw⁻ 2 q72 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q65 ∷
   rw⁻ 4 q73 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q65 ∷
   rw⁻ 6 q73 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q65 ∷
   rw⁻ 8 q72 ∷
   rw⁻ 9 q74 ∷
   rw 2 q75 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q77 ∷
   rw 3 q65 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 1886 W
  q83 : Eqn
  q83 = sE 1481 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-III-units-2
  q84 : Eqn
  q84 = wE 1887 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01] [X3 TOFF213 X3]: 3 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF213-X3 : ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两") ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF213-X3 = derive (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乥丞") (ℓ "丞乥丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两")
  (rw 29 q82 ∷
   rw 0 q83 ∷
   rw 0 q84 ∷ []) Eq.refl
