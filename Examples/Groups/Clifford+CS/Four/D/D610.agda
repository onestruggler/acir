{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD610 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D610 (W : Ws) (Sᴰ : SD610) where

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
  lem-pass-CS03-vs-CZ13 : St 1341
  lem-pass-CS03-vs-CZ13 = pickᴰ 8 Sᴰ
  lem-pass-CS03-vs-CZ23 : St 1342
  lem-pass-CS03-vs-CZ23 = pickᴰ 9 Sᴰ
  lem-pass-CS03-vs-Z1 : St 1343
  lem-pass-CS03-vs-Z1 = pickᴰ 10 Sᴰ
  lem-pass-CS03-vs-Z2 : St 1344
  lem-pass-CS03-vs-Z2 = pickᴰ 11 Sᴰ
  lem-pass-CS03-vs-Z3 : St 1345
  lem-pass-CS03-vs-Z3 = pickᴰ 12 Sᴰ
  lem-pass-CS03-vs-iI : St 1346
  lem-pass-CS03-vs-iI = pickᴰ 13 Sᴰ
  lem-pass-CSd03-vs-CZ13 : St 1347
  lem-pass-CSd03-vs-CZ13 = pickᴰ 14 Sᴰ
  lem-pass-CSd03-vs-CZ23 : St 1348
  lem-pass-CSd03-vs-CZ23 = pickᴰ 15 Sᴰ
  lem-pass-CSd03-vs-Z1 : St 1349
  lem-pass-CSd03-vs-Z1 = pickᴰ 16 Sᴰ
  lem-pass-CSd03-vs-Z2 : St 1350
  lem-pass-CSd03-vs-Z2 = pickᴰ 17 Sᴰ
  lem-pass-CSd03-vs-Z3 : St 1351
  lem-pass-CSd03-vs-Z3 = pickᴰ 18 Sᴰ
  lem-pass-CSd03-vs-iI : St 1352
  lem-pass-CSd03-vs-iI = pickᴰ 19 Sᴰ
  lem-pass-TOFF012-vs-CZ12 : St 1353
  lem-pass-TOFF012-vs-CZ12 = pickᴰ 20 Sᴰ
  lem-pass-TOFF012-vs-Z1 : St 1354
  lem-pass-TOFF012-vs-Z1 = pickᴰ 21 Sᴰ
  lem-pass-TOFF012-vs-Z2 : St 1355
  lem-pass-TOFF012-vs-Z2 = pickᴰ 22 Sᴰ
  lem-pass-TOFF012-vs-Z3 : St 1356
  lem-pass-TOFF012-vs-Z3 = pickᴰ 23 Sᴰ
  lem-pass-TOFF012-vs-iI : St 1357
  lem-pass-TOFF012-vs-iI = pickᴰ 24 Sᴰ
  lem-pass-CCZ123-vs-CCZ023 : St 922
  lem-pass-CCZ123-vs-CCZ023 = pickᴰ 25 Sᴰ
  lem-pass-CCZ023-vs-CZ13 : St 1256
  lem-pass-CCZ023-vs-CZ13 = pickᴰ 26 Sᴰ
  lem-pass-CS03-vs-CZ12 : St 1358
  lem-pass-CS03-vs-CZ12 = pickᴰ 27 Sᴰ
  lem-pass-CSd03-vs-CZ12 : St 1359
  lem-pass-CSd03-vs-CZ12 = pickᴰ 28 Sᴰ
  lem-pass-CCZ012-vs-CCZ013 : St 1107
  lem-pass-CCZ012-vs-CCZ013 = pickᴰ 29 Sᴰ
  lem-pass-TOFF012-vs-CCZ123 : St 1118
  lem-pass-TOFF012-vs-CCZ123 = pickᴰ 30 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 31 Sᴰ
  lem-T-CZ03-T-at1023 : St 1360
  lem-T-CZ03-T-at1023 = pickᴰ 32 Sᴰ
  lem-pass-CS03-vs-CCZ123 : St 1361
  lem-pass-CS03-vs-CCZ123 = pickᴰ 33 Sᴰ
  lem-pass-CSd03-vs-CCZ123 : St 1362
  lem-pass-CSd03-vs-CCZ123 = pickᴰ 34 Sᴰ
  lem-pass-TOFF012-vs-CZ13 : St 1363
  lem-pass-TOFF012-vs-CZ13 = pickᴰ 35 Sᴰ
  lem-pass-TOFF012-vs-CZ23 : St 1364
  lem-pass-TOFF012-vs-CZ23 = pickᴰ 36 Sᴰ
  lem-pass-X3-CK30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : St 1365
  lem-pass-X3-CK30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = pickᴰ 37 Sᴰ

private
  q1 : Eqn
  q1 = sE 1333 lem-pass-CCZ123-vs-CS13
  q2 : Eqn
  q2 = sE 1337 lem-pass-CZ13-vs-CS13
  q3 : Eqn
  q3 = sE 1335 lem-pass-CZ12-vs-CS13
  q4 : Eqn
  q4 = sE 1339 lem-pass-Z1-vs-CS13
  q5 : Eqn
  q5 = wE 1377 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = wE 127 W
  q8 : Eqn
  q8 = wE 271 W
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = wE 8 W
  q11 : Eqn
  q11 = wE 9 W
  q12 : Eqn
  q12 = wE 10 W
  q13 : Eqn
  q13 = wE 272 W
  q14 : Eqn
  q14 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 253 W
  q16 : Eqn
  q16 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q17 : Eqn
  q17 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q18 : Eqn
  q18 = wE 24 W
  q19 : Eqn
  q19 = wE 25 W
  q20 : Eqn
  q20 = wE 26 W
  q21 : Eqn
  q21 = wE 12 W
  q22 : Eqn
  q22 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q23 : Eqn
  q23 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q24 : Eqn
  q24 = wE 14 W
  q25 : Eqn
  q25 = wE 15 W
  q26 : Eqn
  q26 = wE 16 W
  q27 : Eqn
  q27 = wE 46 W
  q28 : Eqn
  q28 = wE 30 W
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 31 W
  q31 : Eqn
  q31 = wE 22 W
  q32 : Eqn
  q32 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q33 : Eqn
  q33 = wE 23 W
  q34 : Eqn
  q34 = wE 47 W
  q35 : Eqn
  q35 = wE 48 W
  q36 : Eqn
  q36 = wE 1 W
  q37 : Eqn
  q37 = wE 3 W
  q38 : Eqn
  q38 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q39 : Eqn
  q39 = wE 43 W
  q40 : Eqn
  q40 = eqn (ℓ "九乚九") (ℓ "乚乜") (ax toff-ccz)
  q41 : Eqn
  q41 = wE 20 W
  q42 : Eqn
  q42 = wE 21 W
  q43 : Eqn
  q43 = wE 49 W
  q44 : Eqn
  q44 = wE 50 W
  q45 : Eqn
  q45 = wE 51 W
  q46 : Eqn
  q46 = wE 52 W
  q47 : Eqn
  q47 = sE 1360 lem-T-CZ03-T-at1023
  q48 : Eqn
  q48 = wE 1806 W
  q49 : Eqn
  q49 = wE 1807 W
  q50 : Eqn
  q50 = sE 1256 lem-pass-CCZ023-vs-CZ13
  q51 : Eqn
  q51 = sE 922 lem-pass-CCZ123-vs-CCZ023
  q52 : Eqn
  q52 = wE 1808 W
  q53 : Eqn
  q53 = wE 74 W
  q54 : Eqn
  q54 = wE 33 W
  q55 : Eqn
  q55 = sE 1334 lem-pass-CCZ123-vs-CSd13
  q56 : Eqn
  q56 = sE 1338 lem-pass-CZ13-vs-CSd13
  q57 : Eqn
  q57 = sE 1336 lem-pass-CZ12-vs-CSd13
  q58 : Eqn
  q58 = sE 1340 lem-pass-Z1-vs-CSd13

-- pass [Z1 CZ12 CZ13 CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 526 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "专丸丿乜丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习专丸丿乜") ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "专丸丿乜丽习举习") (ℓ "丽习举习专丸丿乜")
  (rw 3 q1 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw 0 q4 ∷
   rw 4 q5 ∷
   rw 8 q6 ∷
   re 7 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   rw 9 q10 ∷
   rw 8 q12 ∷
   rw 7 q8 ∷
   rw 8 q13 ∷
   re 8 8 (ℓ "九") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw⁻ 12 q14 ∷
   rw 11 q12 ∷
   rw⁻ 10 q14 ∷
   re 11 3 (ℓ "中") ∷
   rw 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw 7 q15 ∷
   rw⁻ 6 q17 ∷
   rw 7 q6 ∷
   rw 8 q17 ∷
   rw 9 q18 ∷
   rw 10 q16 ∷
   rw 11 q18 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q14 ∷
   rw 13 q19 ∷
   rw 14 q14 ∷
   re 12 3 (ℓ "丽") ∷
   rw 8 q20 ∷
   re 8 5 (ℓ "乜") ∷
   re 7 3 (ℓ "乛") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q10 ∷
   rw 8 q11 ∷
   rw 7 q10 ∷
   rw 6 q12 ∷
   rw 5 q8 ∷
   rw 6 q13 ∷
   re 6 8 (ℓ "九") ∷
   rw 9 q21 ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 15 q24 ∷
   rw 12 q21 ∷
   re 13 3 (ℓ "个") ∷
   rw 11 q25 ∷
   rw 10 q21 ∷
   re 11 3 (ℓ "个") ∷
   rw 9 q26 ∷
   rw 8 q23 ∷
   rw 9 q27 ∷
   re 9 8 (ℓ "九") ∷
   re 7 1 (ℓ "並乜並") ∷
   re 8 1 (ℓ "义丹乊丹丽") ∷
   rw 7 q17 ∷
   rw 8 q28 ∷
   rw 9 q16 ∷
   rw 10 q28 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q14 ∷
   rw 12 q29 ∷
   rw 13 q14 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q30 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q31 ∷
   rw 13 q32 ∷
   rw 11 q33 ∷
   re 12 5 (ℓ "中") ∷
   re 10 1 (ℓ "丼丣丼") ∷
   rw 12 q24 ∷
   rw 9 q34 ∷
   re 8 1 (ℓ "丼丣丼") ∷
   rw 10 q24 ∷
   rw 7 q35 ∷
   rw 8 q36 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q37 ∷
   rw⁻ 10 q38 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q37 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q37 ∷
   rw 9 q39 ∷
   re 9 5 (ℓ "乙") ∷
   re 8 3 (ℓ "乚") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 13 q22 ∷
   rw 12 q23 ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 13 q24 ∷
   rw 10 q21 ∷
   re 11 3 (ℓ "个") ∷
   rw 9 q25 ∷
   rw 8 q21 ∷
   re 9 3 (ℓ "个") ∷
   rw 7 q26 ∷
   rw 6 q23 ∷
   rw 7 q27 ∷
   re 7 8 (ℓ "九") ∷
   rw 7 q40 ∷
   re 7 1 (ℓ "乏乙乏") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q36 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q38 ∷
   rw 11 q36 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q38 ∷
   rw 13 q36 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q37 ∷
   rw 6 q41 ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "个") ∷
   rw 8 q42 ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "个") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q31 ∷
   rw⁻ 12 q32 ∷
   rw 13 q33 ∷
   re 10 5 (ℓ "中") ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw 9 q16 ∷
   rw 10 q18 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q14 ∷
   rw 12 q19 ∷
   rw 13 q14 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q20 ∷
   re 7 5 (ℓ "乜") ∷
   re 6 3 (ℓ "乛") ∷
   re 8 1 (ℓ "义丹乊丹丽") ∷
   rw 7 q43 ∷
   rw 8 q44 ∷
   rw 9 q45 ∷
   rw 10 q44 ∷
   rw 11 q41 ∷
   rw 7 q46 ∷
   re 7 5 (ℓ "乜") ∷
   rw 8 q24 ∷
   re 6 1 (ℓ "並乜並") ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q17 ∷
   rw 7 q28 ∷
   rw 8 q16 ∷
   rw 9 q28 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q14 ∷
   rw 11 q29 ∷
   rw 12 q14 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q30 ∷
   rw 5 q17 ∷
   rw 6 q18 ∷
   rw 7 q16 ∷
   rw 8 q18 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q14 ∷
   rw 10 q19 ∷
   rw 11 q14 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q20 ∷
   re 5 5 (ℓ "乜") ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q17 ∷
   rw 7 q28 ∷
   rw 8 q16 ∷
   rw 9 q28 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q14 ∷
   rw 11 q29 ∷
   rw 12 q14 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q6 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw 9 q16 ∷
   rw 10 q18 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q14 ∷
   rw 12 q19 ∷
   rw 13 q14 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q20 ∷
   re 7 5 (ℓ "乜") ∷
   re 6 3 (ℓ "乛") ∷
   rw 7 q30 ∷
   rw 3 q5 ∷
   rw 4 q47 ∷
   rw 2 q48 ∷
   rw 1 q49 ∷
   rw 6 q50 ∷
   rw 8 q51 ∷
   rw 3 q52 ∷
   rw 7 q6 ∷
   re 6 1 (ℓ "並乜並") ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q17 ∷
   rw 7 q28 ∷
   rw 8 q16 ∷
   rw 9 q28 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q14 ∷
   rw 11 q29 ∷
   rw 12 q14 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q30 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q14 ∷
   rw 11 q9 ∷
   rw⁻ 10 q14 ∷
   re 11 3 (ℓ "丽") ∷
   rw 9 q53 ∷
   rw⁻ 8 q16 ∷
   rw 7 q53 ∷
   rw⁻ 6 q17 ∷
   rw 7 q20 ∷
   re 7 5 (ℓ "乜") ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q17 ∷
   rw 6 q28 ∷
   rw 7 q16 ∷
   rw 8 q28 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q14 ∷
   rw 10 q29 ∷
   rw 11 q14 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q30 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q14 ∷
   rw 10 q9 ∷
   rw⁻ 9 q14 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q53 ∷
   rw⁻ 7 q16 ∷
   rw 6 q53 ∷
   rw⁻ 5 q17 ∷
   rw 6 q20 ∷
   re 6 5 (ℓ "乜") ∷
   rw 6 q54 ∷
   rw 5 q30 ∷
   rw 5 q55 ∷
   rw 4 q56 ∷
   rw 3 q57 ∷
   rw 2 q58 ∷
   rw 6 q5 ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 16 q7 ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   rw 11 q10 ∷
   rw 10 q12 ∷
   rw 9 q8 ∷
   rw 10 q13 ∷
   re 10 8 (ℓ "九") ∷
   re 8 1 (ℓ "义丹乊丹丽") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw⁻ 14 q14 ∷
   rw 13 q12 ∷
   rw⁻ 12 q14 ∷
   re 13 3 (ℓ "中") ∷
   rw 11 q15 ∷
   rw⁻ 10 q16 ∷
   rw 9 q15 ∷
   rw⁻ 8 q17 ∷
   rw 9 q6 ∷
   rw 10 q17 ∷
   rw 11 q18 ∷
   rw 12 q16 ∷
   rw 13 q18 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q14 ∷
   rw 15 q19 ∷
   rw 16 q14 ∷
   re 14 3 (ℓ "丽") ∷
   rw 10 q20 ∷
   re 10 5 (ℓ "乜") ∷
   re 9 3 (ℓ "乛") ∷
   re 7 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   rw 9 q10 ∷
   rw 8 q12 ∷
   rw 7 q8 ∷
   rw 8 q13 ∷
   re 8 8 (ℓ "九") ∷
   rw 11 q21 ∷
   re 10 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 17 q22 ∷
   rw 16 q23 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 17 q24 ∷
   rw 14 q21 ∷
   re 15 3 (ℓ "个") ∷
   rw 13 q25 ∷
   rw 12 q21 ∷
   re 13 3 (ℓ "个") ∷
   rw 11 q26 ∷
   rw 10 q23 ∷
   rw 11 q27 ∷
   re 11 8 (ℓ "九") ∷
   re 9 1 (ℓ "並乜並") ∷
   re 10 1 (ℓ "义丹乊丹丽") ∷
   rw 9 q17 ∷
   rw 10 q28 ∷
   rw 11 q16 ∷
   rw 12 q28 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q14 ∷
   rw 14 q29 ∷
   rw 15 q14 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q30 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q31 ∷
   rw 15 q32 ∷
   rw 13 q33 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "丼丣丼") ∷
   rw 14 q24 ∷
   rw 11 q34 ∷
   re 10 1 (ℓ "丼丣丼") ∷
   rw 12 q24 ∷
   rw 9 q35 ∷
   rw 10 q36 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q37 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q37 ∷
   rw⁻ 14 q38 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q37 ∷
   rw 11 q39 ∷
   re 11 5 (ℓ "乙") ∷
   re 10 3 (ℓ "乚") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 15 q24 ∷
   rw 12 q21 ∷
   re 13 3 (ℓ "个") ∷
   rw 11 q25 ∷
   rw 10 q21 ∷
   re 11 3 (ℓ "个") ∷
   rw 9 q26 ∷
   rw 8 q23 ∷
   rw 9 q27 ∷
   re 9 8 (ℓ "九") ∷
   rw 9 q40 ∷
   re 9 1 (ℓ "乏乙乏") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 11 q36 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q38 ∷
   rw 13 q36 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q38 ∷
   rw 15 q36 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q37 ∷
   rw 8 q41 ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "个") ∷
   rw 10 q42 ∷
   rw 13 q21 ∷
   re 11 3 (ℓ "个") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q31 ∷
   rw⁻ 14 q32 ∷
   rw 15 q33 ∷
   re 12 5 (ℓ "中") ∷
   rw 8 q6 ∷
   rw 9 q17 ∷
   rw 10 q18 ∷
   rw 11 q16 ∷
   rw 12 q18 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q14 ∷
   rw 14 q19 ∷
   rw 15 q14 ∷
   re 13 3 (ℓ "丽") ∷
   rw 9 q20 ∷
   re 9 5 (ℓ "乜") ∷
   re 8 3 (ℓ "乛") ∷
   re 10 1 (ℓ "义丹乊丹丽") ∷
   rw 9 q43 ∷
   rw 10 q44 ∷
   rw 11 q45 ∷
   rw 12 q44 ∷
   rw 13 q41 ∷
   rw 9 q46 ∷
   re 9 5 (ℓ "乜") ∷
   rw 10 q24 ∷
   re 8 1 (ℓ "並乜並") ∷
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q17 ∷
   rw 9 q28 ∷
   rw 10 q16 ∷
   rw 11 q28 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q14 ∷
   rw 13 q29 ∷
   rw 14 q14 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q30 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw 9 q16 ∷
   rw 10 q18 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q14 ∷
   rw 12 q19 ∷
   rw 13 q14 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q20 ∷
   re 7 5 (ℓ "乜") ∷
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q17 ∷
   rw 9 q28 ∷
   rw 10 q16 ∷
   rw 11 q28 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q14 ∷
   rw 13 q29 ∷
   rw 14 q14 ∷
   re 12 3 (ℓ "中") ∷
   rw 8 q6 ∷
   rw 9 q17 ∷
   rw 10 q18 ∷
   rw 11 q16 ∷
   rw 12 q18 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q14 ∷
   rw 14 q19 ∷
   rw 15 q14 ∷
   re 13 3 (ℓ "丽") ∷
   rw 9 q20 ∷
   re 9 5 (ℓ "乜") ∷
   re 8 3 (ℓ "乛") ∷
   rw 9 q30 ∷
   rw 5 q5 ∷
   rw 6 q47 ∷
   rw 4 q48 ∷
   rw 3 q49 ∷
   rw 8 q50 ∷
   rw 10 q51 ∷
   rw 5 q52 ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "並乜並") ∷
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q17 ∷
   rw 9 q28 ∷
   rw 10 q16 ∷
   rw 11 q28 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q14 ∷
   rw 13 q29 ∷
   rw 14 q14 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q30 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q14 ∷
   rw 13 q9 ∷
   rw⁻ 12 q14 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q53 ∷
   rw⁻ 10 q16 ∷
   rw 9 q53 ∷
   rw⁻ 8 q17 ∷
   rw 9 q20 ∷
   re 9 5 (ℓ "乜") ∷
   re 7 1 (ℓ "並乜並") ∷
   re 8 1 (ℓ "义丹乊丹丽") ∷
   rw 7 q17 ∷
   rw 8 q28 ∷
   rw 9 q16 ∷
   rw 10 q28 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q14 ∷
   rw 12 q29 ∷
   rw 13 q14 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q30 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q14 ∷
   rw 12 q9 ∷
   rw⁻ 11 q14 ∷
   re 12 3 (ℓ "丽") ∷
   rw 10 q53 ∷
   rw⁻ 9 q16 ∷
   rw 8 q53 ∷
   rw⁻ 7 q17 ∷
   rw 8 q20 ∷
   re 8 5 (ℓ "乜") ∷
   rw 8 q54 ∷
   rw 7 q30 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 1535 W
  q60 : Eqn
  q60 = wE 1809 W
  q61 : Eqn
  q61 = eqn (ℓ "乙丝") (ℓ "丝乙") (low₃-comm (CCZ) ((K • iI)))
  q62 : Eqn
  q62 = wE 1810 W
  q63 : Eqn
  q63 = sE 1107 lem-pass-CCZ012-vs-CCZ013
  q64 : Eqn
  q64 = wE 1811 W
  q65 : Eqn
  q65 = eqn (ℓ "乙东") (ℓ "东乙") (low₃-comm (CCZ) (K))
  q66 : Eqn
  q66 = wE 1294 W
  q67 : Eqn
  q67 = wE 1538 W

-- pass [TOFF201] [CCZ013]: 13 steps
lem-pass-TOFF201-vs-CCZ013 : ⟪ (ℓ "乣乚") ⟫ʷ ≈ ⟪ (ℓ "乚乣") ⟫ʷ
lem-pass-TOFF201-vs-CCZ013 = derive (ℓ "乣乚") (ℓ "乚乣")
  (rw 0 q59 ∷
   re 3 1 (ℓ "乏乙乏") ∷
   rw 2 q60 ∷
   rw⁻ 3 q61 ∷
   rw 4 q62 ∷
   re 2 3 (ℓ "乚") ∷
   rw 1 q63 ∷
   re 1 1 (ℓ "乏乙乏") ∷
   rw 0 q64 ∷
   rw⁻ 1 q65 ∷
   rw 2 q66 ∷
   re 0 3 (ℓ "乚") ∷
   rw 1 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = sE 1346 lem-pass-CS03-vs-iI
  q69 : Eqn
  q69 = sE 1343 lem-pass-CS03-vs-Z1
  q70 : Eqn
  q70 = sE 1344 lem-pass-CS03-vs-Z2
  q71 : Eqn
  q71 = sE 1358 lem-pass-CS03-vs-CZ12
  q72 : Eqn
  q72 = sE 1345 lem-pass-CS03-vs-Z3
  q73 : Eqn
  q73 = sE 1341 lem-pass-CS03-vs-CZ13
  q74 : Eqn
  q74 = sE 1342 lem-pass-CS03-vs-CZ23
  q75 : Eqn
  q75 = sE 1361 lem-pass-CS03-vs-CCZ123

-- pass [CS03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (ℓ "中一一专丙丸丟丿之乜") ⟫ʷ ≈ ⟪ (ℓ "一一专丙丸丟丿之乜中") ⟫ʷ
lem-pass-CS03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (ℓ "中一一专丙丸丟丿之乜") (ℓ "一一专丙丸丟丿之乜中")
  (rw 0 q68 ∷
   rw 1 q68 ∷
   rw 2 q69 ∷
   rw 3 q70 ∷
   rw 4 q71 ∷
   rw 5 q72 ∷
   rw 6 q73 ∷
   rw 7 q74 ∷
   rw 8 q75 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = sE 1357 lem-pass-TOFF012-vs-iI
  q77 : Eqn
  q77 = sE 1354 lem-pass-TOFF012-vs-Z1
  q78 : Eqn
  q78 = sE 1355 lem-pass-TOFF012-vs-Z2
  q79 : Eqn
  q79 = sE 1353 lem-pass-TOFF012-vs-CZ12
  q80 : Eqn
  q80 = sE 1356 lem-pass-TOFF012-vs-Z3
  q81 : Eqn
  q81 = sE 1363 lem-pass-TOFF012-vs-CZ13
  q82 : Eqn
  q82 = sE 1364 lem-pass-TOFF012-vs-CZ23
  q83 : Eqn
  q83 = sE 1118 lem-pass-TOFF012-vs-CCZ123

-- pass [TOFF012] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (ℓ "九一一专丙丸丟丿之乜") ⟫ʷ ≈ ⟪ (ℓ "一一专丙丸丟丿之乜九") ⟫ʷ
lem-pass-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (ℓ "九一一专丙丸丟丿之乜") (ℓ "一一专丙丸丟丿之乜九")
  (rw 0 q76 ∷
   rw 1 q76 ∷
   rw 2 q77 ∷
   rw 3 q78 ∷
   rw 4 q79 ∷
   rw 5 q80 ∷
   rw 6 q81 ∷
   rw 7 q82 ∷
   rw 8 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = sE 1352 lem-pass-CSd03-vs-iI
  q85 : Eqn
  q85 = sE 1349 lem-pass-CSd03-vs-Z1
  q86 : Eqn
  q86 = sE 1350 lem-pass-CSd03-vs-Z2
  q87 : Eqn
  q87 = sE 1359 lem-pass-CSd03-vs-CZ12
  q88 : Eqn
  q88 = sE 1351 lem-pass-CSd03-vs-Z3
  q89 : Eqn
  q89 = sE 1347 lem-pass-CSd03-vs-CZ13
  q90 : Eqn
  q90 = sE 1348 lem-pass-CSd03-vs-CZ23
  q91 : Eqn
  q91 = sE 1362 lem-pass-CSd03-vs-CCZ123

-- pass [CSd03] [iI iI Z1 Z2 CZ12 Z3 CZ13 CZ23 CCZ123]: 9 steps
lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : ⟪ (ℓ "丮一一专丙丸丟丿之乜") ⟫ʷ ≈ ⟪ (ℓ "一一专丙丸丟丿之乜丮") ⟫ʷ
lem-pass-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = derive (ℓ "丮一一专丙丸丟丿之乜") (ℓ "一一专丙丸丟丿之乜丮")
  (rw 0 q84 ∷
   rw 1 q84 ∷
   rw 2 q85 ∷
   rw 3 q86 ∷
   rw 4 q87 ∷
   rw 5 q88 ∷
   rw 6 q89 ∷
   rw 7 q90 ∷
   rw 8 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q93 : Eqn
  q93 = wE 173 W
  q94 : Eqn
  q94 = wE 1676 W
  q95 : Eqn
  q95 = wE 175 W
  q96 : Eqn
  q96 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q97 : Eqn
  q97 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q98 : Eqn
  q98 = wE 137 W
  q99 : Eqn
  q99 = wE 1677 W
  q100 : Eqn
  q100 = wE 139 W
  q101 : Eqn
  q101 = wE 1485 W
  q102 : Eqn
  q102 = sE 1146 lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X3 CKd30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CKd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (ℓ "丞乒丞丒丘中九丮九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘中九丮九丒丘丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = derive (ℓ "丞乒丞丒丘中九丮九丒丘") (ℓ "丒丘中九丮九丒丘丞乒丞")
  (rw 4 q36 ∷
   rw 3 q92 ∷
   rw 2 q93 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw 3 q37 ∷
   rw 0 q93 ∷
   rw 1 q94 ∷
   rw⁻ 0 q92 ∷
   rw 1 q95 ∷
   rw 4 q36 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q95 ∷
   rw 4 q37 ∷
   rw 5 q6 ∷
   rw⁻ 4 q96 ∷
   rw⁻ 3 q97 ∷
   re 2 1 (ℓ "乏久乏") ∷
   rw⁻ 4 q14 ∷
   rw 3 q98 ∷
   rw⁻ 2 q14 ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 1 q97 ∷
   rw 2 q99 ∷
   rw 1 q96 ∷
   rw 2 q97 ∷
   re 4 1 (ℓ "乏么乏") ∷
   rw 3 q14 ∷
   rw 4 q100 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "乒") ∷
   rw 4 q97 ∷
   rw 5 q30 ∷
   rw 5 q36 ∷
   rw 4 q93 ∷
   re 3 1 (ℓ "乏久乏") ∷
   rw 5 q37 ∷
   rw 2 q93 ∷
   rw 3 q101 ∷
   rw 2 q95 ∷
   rw 5 q36 ∷
   re 3 3 (ℓ "乒") ∷
   rw 4 q95 ∷
   rw 5 q37 ∷
   rw 2 q102 ∷
   rw 9 q36 ∷
   rw 8 q93 ∷
   re 7 1 (ℓ "乏久乏") ∷
   rw 9 q37 ∷
   rw 6 q93 ∷
   rw 7 q101 ∷
   rw 6 q95 ∷
   rw 9 q36 ∷
   re 7 3 (ℓ "乒") ∷
   rw 8 q95 ∷
   rw 9 q37 ∷
   rw 10 q36 ∷
   rw 9 q92 ∷
   rw 8 q93 ∷
   re 7 1 (ℓ "乏久乏") ∷
   rw 9 q37 ∷
   rw 6 q93 ∷
   rw 7 q94 ∷
   rw⁻ 6 q92 ∷
   rw 7 q95 ∷
   rw 10 q36 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q95 ∷
   rw 10 q37 ∷
   rw 11 q6 ∷
   rw⁻ 10 q96 ∷
   rw⁻ 9 q97 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw⁻ 10 q14 ∷
   rw 9 q98 ∷
   rw⁻ 8 q14 ∷
   re 9 3 (ℓ "乕") ∷
   rw⁻ 7 q97 ∷
   rw 8 q99 ∷
   rw 7 q96 ∷
   rw 8 q97 ∷
   re 10 1 (ℓ "乏么乏") ∷
   rw 9 q14 ∷
   rw 10 q100 ∷
   rw 11 q14 ∷
   re 9 3 (ℓ "乒") ∷
   rw 10 q97 ∷
   rw 11 q30 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q104 : Eqn
  q104 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q105 : Eqn
  q105 = wE 1407 W
  q106 : Eqn
  q106 = sE 1365 lem-pass-X3-CK30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2
  q107 : Eqn
  q107 = wE 1408 W

-- pass [CK30] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 27 steps
lem-pass-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "乑丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞乑") ⟫ʷ
lem-pass-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "乑丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞乑")
  (rw 2 q103 ∷
   rw 1 q104 ∷
   rw 2 q36 ∷
   rw 1 q93 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q37 ∷
   rw 1 q105 ∷
   rw 0 q95 ∷
   rw 1 q95 ∷
   rw 4 q36 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q95 ∷
   rw 4 q37 ∷
   rw 1 q106 ∷
   rw 13 q36 ∷
   rw 12 q93 ∷
   rw 11 q93 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q37 ∷
   rw 9 q93 ∷
   rw 10 q107 ∷
   rw 9 q95 ∷
   rw 12 q36 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q37 ∷
   rw⁻ 0 q104 ∷
   rw⁻ 1 q103 ∷ []) Eq.refl
