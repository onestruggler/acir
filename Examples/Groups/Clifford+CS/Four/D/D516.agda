{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD516 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D516 (W : Ws) (Sᴰ : SD516) where

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
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 0 Sᴰ
  lem-pass-CSd13-vs-S0 : St 64
  lem-pass-CSd13-vs-S0 = pickᴰ 1 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS12 : St 42
  lem-pass-X3-CK30-X3-vs-CS12 = pickᴰ 2 Sᴰ
  lem-pass-X3-CK30-X3-vs-CSd12 : St 43
  lem-pass-X3-CK30-X3-vs-CSd12 = pickᴰ 3 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS12 : St 45
  lem-pass-X3-CKd30-X3-vs-CS12 = pickᴰ 4 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CSd12 : St 46
  lem-pass-X3-CKd30-X3-vs-CSd12 = pickᴰ 5 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS12 : St 48
  lem-pass-X3-CS30-X3-vs-CS12 = pickᴰ 6 Sᴰ
  lem-pass-X3-CS30-X3-vs-CSd12 : St 49
  lem-pass-X3-CS30-X3-vs-CSd12 = pickᴰ 7 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS12 : St 51
  lem-pass-X3-CSd30-X3-vs-CS12 = pickᴰ 8 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CSd12 : St 52
  lem-pass-X3-CSd30-X3-vs-CSd12 = pickᴰ 9 Sᴰ
  lem-pass-CS23-vs-CS01 : St 151
  lem-pass-CS23-vs-CS01 = pickᴰ 10 Sᴰ
  lem-pass-CS23-vs-CSd01 : St 152
  lem-pass-CS23-vs-CSd01 = pickᴰ 11 Sᴰ
  lem-pass-CS23-vs-S1 : St 165
  lem-pass-CS23-vs-S1 = pickᴰ 12 Sᴰ
  lem-pass-CS23-vs-Sd1 : St 166
  lem-pass-CS23-vs-Sd1 = pickᴰ 13 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF203 : St 167
  lem-pass-X3-CK30-X3-vs-TOFF203 = pickᴰ 14 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS01 : St 154
  lem-pass-X3-CK32-X3-vs-CS01 = pickᴰ 15 Sᴰ
  lem-pass-X3-CK32-X3-vs-CSd01 : St 155
  lem-pass-X3-CK32-X3-vs-CSd01 = pickᴰ 16 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF023 : St 156
  lem-pass-X3-CK32-X3-vs-TOFF023 = pickᴰ 17 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF203 : St 168
  lem-pass-X3-CKd30-X3-vs-TOFF203 = pickᴰ 18 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF203 : St 169
  lem-pass-X3-CS30-X3-vs-TOFF203 = pickᴰ 19 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF203 : St 170
  lem-pass-X3-CSd30-X3-vs-TOFF203 = pickᴰ 20 Sᴰ

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
  q26 = sE 165 lem-pass-CS23-vs-S1
  q27 : Eqn
  q27 = sE 152 lem-pass-CS23-vs-CSd01
  q28 : Eqn
  q28 = sE 166 lem-pass-CS23-vs-Sd1
  q29 : Eqn
  q29 = sE 151 lem-pass-CS23-vs-CS01

-- pass [CS23] [X3 TOFF023 X3 S1 CSd01 X3 TOFF023 X3 Sd1 CS01]: 400 steps
lem-pass-CS23-vs-X3-TOFF023-X3-S1-CSd01-X3-TOFF023-X3-Sd1-CS01 : ⟪ (ℓ "义丞也丞与両丞也丞丏丠") ⟫ʷ ≈ ⟪ (ℓ "丞也丞与両丞也丞丏丠义") ⟫ʷ
lem-pass-CS23-vs-X3-TOFF023-X3-S1-CSd01-X3-TOFF023-X3-Sd1-CS01 = derive (ℓ "义丞也丞与両丞也丞丏丠") (ℓ "丞也丞与両丞也丞丏丠义")
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
   rw 4 q27 ∷
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
   rw 7 q1 ∷
   rw 6 q22 ∷
   rw⁻ 5 q4 ∷
   rw 6 q23 ∷
   rw 5 q17 ∷
   rw 6 q4 ∷
   rw 7 q10 ∷
   rw 8 q1 ∷
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
   rw⁻ 6 q4 ∷
   rw 7 q24 ∷
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
   rw 7 q4 ∷
   rw 8 q10 ∷
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
   rw 5 q22 ∷
   rw 6 q25 ∷
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
   rw 8 q28 ∷
   rw 9 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = sE 154 lem-pass-X3-CK32-X3-vs-CS01
  q31 : Eqn
  q31 = sE 156 lem-pass-X3-CK32-X3-vs-TOFF023
  q32 : Eqn
  q32 = sE 155 lem-pass-X3-CK32-X3-vs-CSd01

-- pass [X3 CK32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (ℓ "丞乗丞丠也両也") ⟫ʷ ≈ ⟪ (ℓ "丠也両也丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = derive (ℓ "丞乗丞丠也両也") (ℓ "丠也両也丞乗丞")
  (rw 0 q30 ∷
   rw 1 q31 ∷
   rw 2 q32 ∷
   rw 3 q31 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 42 lem-pass-X3-CK30-X3-vs-CS12
  q34 : Eqn
  q34 = sE 167 lem-pass-X3-CK30-X3-vs-TOFF203
  q35 : Eqn
  q35 = sE 43 lem-pass-X3-CK30-X3-vs-CSd12

-- pass [X3 CK30 X3] [CS12 TOFF203 CSd12 TOFF203]: 4 steps
lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : ⟪ (ℓ "丞乑丞丶乤丷乤") ⟫ʷ ≈ ⟪ (ℓ "丶乤丷乤丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = derive (ℓ "丞乑丞丶乤丷乤") (ℓ "丶乤丷乤丞乑丞")
  (rw 0 q33 ∷
   rw 1 q34 ∷
   rw 2 q35 ∷
   rw 3 q34 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 48 lem-pass-X3-CS30-X3-vs-CS12
  q37 : Eqn
  q37 = sE 169 lem-pass-X3-CS30-X3-vs-TOFF203
  q38 : Eqn
  q38 = sE 49 lem-pass-X3-CS30-X3-vs-CSd12

-- pass [X3 CS30 X3] [CS12 TOFF203 CSd12 TOFF203]: 4 steps
lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : ⟪ (ℓ "丞中丞丶乤丷乤") ⟫ʷ ≈ ⟪ (ℓ "丶乤丷乤丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = derive (ℓ "丞中丞丶乤丷乤") (ℓ "丶乤丷乤丞中丞")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 2 q38 ∷
   rw 3 q37 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 51 lem-pass-X3-CSd30-X3-vs-CS12
  q40 : Eqn
  q40 = sE 170 lem-pass-X3-CSd30-X3-vs-TOFF203
  q41 : Eqn
  q41 = sE 52 lem-pass-X3-CSd30-X3-vs-CSd12

-- pass [X3 CSd30 X3] [CS12 TOFF203 CSd12 TOFF203]: 4 steps
lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : ⟪ (ℓ "丞丮丞丶乤丷乤") ⟫ʷ ≈ ⟪ (ℓ "丶乤丷乤丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = derive (ℓ "丞丮丞丶乤丷乤") (ℓ "丶乤丷乤丞丮丞")
  (rw 0 q39 ∷
   rw 1 q40 ∷
   rw 2 q41 ∷
   rw 3 q40 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = sE 45 lem-pass-X3-CKd30-X3-vs-CS12
  q43 : Eqn
  q43 = sE 168 lem-pass-X3-CKd30-X3-vs-TOFF203
  q44 : Eqn
  q44 = sE 46 lem-pass-X3-CKd30-X3-vs-CSd12

-- pass [X3 CKd30 X3] [CS12 TOFF203 CSd12 TOFF203]: 4 steps
lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 : ⟪ (ℓ "丞乒丞丶乤丷乤") ⟫ʷ ≈ ⟪ (ℓ "丶乤丷乤丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS12-TOFF203-CSd12-TOFF203 = derive (ℓ "丞乒丞丶乤丷乤") (ℓ "丶乤丷乤丞乒丞")
  (rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw 3 q43 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 63 lem-pass-CS13-vs-S0
  q46 : Eqn
  q46 = wE 1368 W
  q47 : Eqn
  q47 = sE 64 lem-pass-CSd13-vs-S0

-- pass [S0] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丈丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丈") ⟫ʷ
lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丈丽习举习") (ℓ "丽习举习丈")
  (rw⁻ 0 q45 ∷
   rw 1 q46 ∷
   rw⁻ 2 q47 ∷
   rw 3 q46 ∷ []) Eq.refl
