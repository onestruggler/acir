{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD514 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D514 (W : Ws) (Sᴰ : SD514) where

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
  lem-pass-CS23-vs-CS01 : St 151
  lem-pass-CS23-vs-CS01 = pickᴰ 0 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 88
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS02 : St 89
  lem-pass-X3-CS31-X3-vs-CS02 = pickᴰ 2 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS02 : St 114
  lem-pass-X3-CK31-X3-vs-CS02 = pickᴰ 3 Sᴰ
  lem-pass-X3-CK31-X3-vs-CSd02 : St 115
  lem-pass-X3-CK31-X3-vs-CSd02 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF013 : St 116
  lem-pass-X3-CK31-X3-vs-TOFF013 = pickᴰ 5 Sᴰ
  lem-pass-X3-CS31-X3-vs-CSd02 : St 120
  lem-pass-X3-CS31-X3-vs-CSd02 = pickᴰ 6 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF013 : St 121
  lem-pass-X3-CS31-X3-vs-TOFF013 = pickᴰ 7 Sᴰ
  lem-pass-CS23-vs-CSd01 : St 152
  lem-pass-CS23-vs-CSd01 = pickᴰ 8 Sᴰ
  lem-comm-CCZ013-CCZ123 : St 153
  lem-comm-CCZ013-CCZ123 = pickᴰ 9 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS01 : St 154
  lem-pass-X3-CK32-X3-vs-CS01 = pickᴰ 10 Sᴰ
  lem-pass-X3-CK32-X3-vs-CSd01 : St 155
  lem-pass-X3-CK32-X3-vs-CSd01 = pickᴰ 11 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF023 : St 156
  lem-pass-X3-CK32-X3-vs-TOFF023 = pickᴰ 12 Sᴰ

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
  q22 = wE 6 W
  q23 : Eqn
  q23 = wE 1327 W
  q24 : Eqn
  q24 = wE 1374 W
  q25 : Eqn
  q25 = wE 1375 W
  q26 : Eqn
  q26 = sE 151 lem-pass-CS23-vs-CS01
  q27 : Eqn
  q27 = sE 152 lem-pass-CS23-vs-CSd01

-- pass [CS23] [X3 TOFF023 X3 CS01 X3 TOFF023 X3 CSd01]: 398 steps
lem-pass-CS23-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 : ⟪ (ℓ "义丞也丞丠丞也丞両") ⟫ʷ ≈ ⟪ (ℓ "丞也丞丠丞也丞両义") ⟫ʷ
lem-pass-CS23-vs-X3-TOFF023-X3-CS01-X3-TOFF023-X3-CSd01 = derive (ℓ "义丞也丞丠丞也丞両") (ℓ "丞也丞丠丞也丞両义")
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
   rw 2 q1 ∷
   rw 1 q22 ∷
   rw⁻ 0 q4 ∷
   rw 1 q23 ∷
   rw 0 q17 ∷
   rw 1 q4 ∷
   rw 2 q10 ∷
   rw 3 q1 ∷
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
   rw⁻ 1 q4 ∷
   rw 2 q24 ∷
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
   rw 2 q4 ∷
   rw 3 q10 ∷
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
   rw 0 q22 ∷
   rw 1 q25 ∷
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
   rw 3 q26 ∷
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
   rw 6 q1 ∷
   rw 5 q22 ∷
   rw⁻ 4 q4 ∷
   rw 5 q23 ∷
   rw 4 q17 ∷
   rw 5 q4 ∷
   rw 6 q10 ∷
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
   rw⁻ 5 q4 ∷
   rw 6 q24 ∷
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
   rw 6 q4 ∷
   rw 7 q10 ∷
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
   rw 4 q22 ∷
   rw 5 q25 ∷
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
   rw 7 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 153 lem-comm-CCZ013-CCZ123

-- pass [CCZ013] [CCZ123]: 1 steps
lem-pass-CCZ013-vs-CCZ123 : ⟪ (ℓ "乚乜") ⟫ʷ ≈ ⟪ (ℓ "乜乚") ⟫ʷ
lem-pass-CCZ013-vs-CCZ123 = derive (ℓ "乚乜") (ℓ "乜乚")
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 156 lem-pass-X3-CK32-X3-vs-TOFF023
  q30 : Eqn
  q30 = sE 154 lem-pass-X3-CK32-X3-vs-CS01
  q31 : Eqn
  q31 = sE 155 lem-pass-X3-CK32-X3-vs-CSd01

-- pass [X3 CK32 X3] [TOFF023 CS01 TOFF023 CSd01]: 4 steps
lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (ℓ "丞乗丞也丠也両") ⟫ʷ ≈ ⟪ (ℓ "也丠也両丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = derive (ℓ "丞乗丞也丠也両") (ℓ "也丠也両丞乗丞")
  (rw 0 q29 ∷
   rw 1 q30 ∷
   rw 2 q29 ∷
   rw 3 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 1376 W
  q33 : Eqn
  q33 = wE 1377 W
  q34 : Eqn
  q34 = wE 1378 W
  q35 : Eqn
  q35 = sE 88 lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q36 : Eqn
  q36 = wE 1379 W
  q37 : Eqn
  q37 = wE 1380 W
  q38 : Eqn
  q38 = wE 1381 W

-- pass [X3 CK31 X3] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞乔丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞乔丞丽习举习") (ℓ "丽习举习丞乔丞")
  (rw 0 q32 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw 3 q33 ∷
   rw⁻ 4 q35 ∷
   rw 10 q36 ∷
   rw 9 q37 ∷
   rw 8 q38 ∷
   rw 7 q37 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 121 lem-pass-X3-CS31-X3-vs-TOFF013
  q40 : Eqn
  q40 = sE 89 lem-pass-X3-CS31-X3-vs-CS02
  q41 : Eqn
  q41 = sE 120 lem-pass-X3-CS31-X3-vs-CSd02

-- pass [X3 CS31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞丽丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞丽丞乞丧乞丨") (ℓ "乞丧乞丨丞丽丞")
  (rw 0 q39 ∷
   rw 1 q40 ∷
   rw 2 q39 ∷
   rw 3 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = sE 116 lem-pass-X3-CK31-X3-vs-TOFF013
  q43 : Eqn
  q43 = sE 114 lem-pass-X3-CK31-X3-vs-CS02
  q44 : Eqn
  q44 = sE 115 lem-pass-X3-CK31-X3-vs-CSd02

-- pass [X3 CK31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞乔丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞乔丞乞丧乞丨") (ℓ "乞丧乞丨丞乔丞")
  (rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q42 ∷
   rw 3 q44 ∷ []) Eq.refl
