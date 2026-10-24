{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD515 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D515 (W : Ws) (Sᴰ : SD515) where

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
  lem-pass-CS13-vs-CS02 : St 27
  lem-pass-CS13-vs-CS02 = pickᴰ 0 Sᴰ
  lem-pass-CSd02-vs-CS13 : St 28
  lem-pass-CSd02-vs-CS13 = pickᴰ 1 Sᴰ
  lem-pass-S2-vs-CS13 : St 30
  lem-pass-S2-vs-CS13 = pickᴰ 2 Sᴰ
  lem-pass-Sd2-vs-CS13 : St 32
  lem-pass-Sd2-vs-CS13 = pickᴰ 3 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS02 : St 117
  lem-pass-X3-CKd31-X3-vs-CS02 = pickᴰ 4 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CSd02 : St 118
  lem-pass-X3-CKd31-X3-vs-CSd02 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF013 : St 119
  lem-pass-X3-CKd31-X3-vs-TOFF013 = pickᴰ 6 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS02 : St 122
  lem-pass-X3-CSd31-X3-vs-CS02 = pickᴰ 7 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CSd02 : St 123
  lem-pass-X3-CSd31-X3-vs-CSd02 = pickᴰ 8 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF013 : St 124
  lem-pass-X3-CSd31-X3-vs-TOFF013 = pickᴰ 9 Sᴰ
  lem-pass-CS23-vs-Sd0 : St 157
  lem-pass-CS23-vs-Sd0 = pickᴰ 10 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS01 : St 139
  lem-pass-X3-CKd32-X3-vs-CS01 = pickᴰ 11 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CSd01 : St 140
  lem-pass-X3-CKd32-X3-vs-CSd01 = pickᴰ 12 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF023 : St 141
  lem-pass-X3-CKd32-X3-vs-TOFF023 = pickᴰ 13 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS01 : St 142
  lem-pass-X3-CS32-X3-vs-CS01 = pickᴰ 14 Sᴰ
  lem-pass-X3-CS32-X3-vs-CSd01 : St 143
  lem-pass-X3-CS32-X3-vs-CSd01 = pickᴰ 15 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF023 : St 144
  lem-pass-X3-CS32-X3-vs-TOFF023 = pickᴰ 16 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS01 : St 145
  lem-pass-X3-CSd32-X3-vs-CS01 = pickᴰ 17 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CSd01 : St 147
  lem-pass-X3-CSd32-X3-vs-CSd01 = pickᴰ 18 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF023 : St 149
  lem-pass-X3-CSd32-X3-vs-TOFF023 = pickᴰ 19 Sᴰ
  lem-comm-CCZ023-CS13 : St 158
  lem-comm-CCZ023-CS13 = pickᴰ 20 Sᴰ
  lem-pass-CS23-vs-Sd3 : St 159
  lem-pass-CS23-vs-Sd3 = pickᴰ 21 Sᴰ
  lem-pass-CS23-vs-iI : St 160
  lem-pass-CS23-vs-iI = pickᴰ 22 Sᴰ
  lem-pass-CSd23-vs-iI : St 161
  lem-pass-CSd23-vs-iI = pickᴰ 23 Sᴰ
  lem-pass-Sd0-vs-CSd23 : St 162
  lem-pass-Sd0-vs-CSd23 = pickᴰ 24 Sᴰ
  lem-pass-Sd3-vs-CSd23 : St 163
  lem-pass-Sd3-vs-CSd23 = pickᴰ 25 Sᴰ
  lem-pass-TOFF201-vs-iI : St 164
  lem-pass-TOFF201-vs-iI = pickᴰ 26 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = wE 1362 W
  q9 : Eqn
  q9 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q10 : Eqn
  q10 = wE 1382 W
  q11 : Eqn
  q11 = wE 90 W
  q12 : Eqn
  q12 = wE 1364 W
  q13 : Eqn
  q13 = wE 175 W
  q14 : Eqn
  q14 = sE 30 lem-pass-S2-vs-CS13
  q15 : Eqn
  q15 = sE 28 lem-pass-CSd02-vs-CS13
  q16 : Eqn
  q16 = sE 32 lem-pass-Sd2-vs-CS13
  q17 : Eqn
  q17 = sE 27 lem-pass-CS13-vs-CS02

-- pass [CS13] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 384 steps
lem-pass-CS13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (ℓ "丽丞乞丞且丨丞乞丞丕丧") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞且丨丞乞丞丕丧丽") ⟫ʷ
lem-pass-CS13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = derive (ℓ "丽丞乞丞且丨丞乞丞丕丧") (ℓ "丞乞丞且丨丞乞丞丕丧丽")
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q9 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw 3 q6 ∷
   rw 2 q1 ∷
   rw 1 q9 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q6 ∷
   rw 1 q10 ∷
   rw⁻ 0 q9 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q6 ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw 2 q11 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q6 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏九乏") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q9 ∷
   rw 1 q12 ∷
   rw 0 q13 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q13 ∷
   rw 3 q6 ∷
   rw⁻ 3 q14 ∷
   rw⁻ 4 q15 ∷
   rw 9 q1 ∷
   rw 8 q2 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   rw 11 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 7 q3 ∷
   rw 8 q7 ∷
   re 8 8 (ℓ "九") ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw⁻ 6 q9 ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q1 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw⁻ 12 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q5 ∷
   rw 8 q7 ∷
   re 8 8 (ℓ "九") ∷
   re 7 3 (ℓ "乞") ∷
   rw 8 q6 ∷
   rw 7 q1 ∷
   rw 6 q9 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 6 q10 ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q6 ∷
   rw 8 q1 ∷
   re 7 1 (ℓ "乏九乏") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   rw 11 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 7 q3 ∷
   rw 8 q7 ∷
   re 8 8 (ℓ "九") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 7 q11 ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q7 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q6 ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏九乏") ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 6 q3 ∷
   rw 7 q7 ∷
   re 7 8 (ℓ "九") ∷
   rw 5 q9 ∷
   rw 6 q12 ∷
   rw 5 q13 ∷
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q7 ∷
   re 7 8 (ℓ "九") ∷
   re 6 3 (ℓ "乞") ∷
   rw 7 q13 ∷
   rw 8 q6 ∷
   rw⁻ 8 q16 ∷
   rw 9 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = sE 158 lem-comm-CCZ023-CS13

-- pass [CCZ023] [CS13]: 1 steps
lem-pass-CCZ023-vs-CS13 : ⟪ (ℓ "乛丽") ⟫ʷ ≈ ⟪ (ℓ "丽乛") ⟫ʷ
lem-pass-CCZ023-vs-CS13 = derive (ℓ "乛丽") (ℓ "丽乛")
  (rw 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 119 lem-pass-X3-CKd31-X3-vs-TOFF013
  q20 : Eqn
  q20 = sE 117 lem-pass-X3-CKd31-X3-vs-CS02
  q21 : Eqn
  q21 = sE 118 lem-pass-X3-CKd31-X3-vs-CSd02

-- pass [X3 CKd31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CKd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞乕丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞乕丞乞丧乞丨") (ℓ "乞丧乞丨丞乕丞")
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 2 q19 ∷
   rw 3 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 124 lem-pass-X3-CSd31-X3-vs-TOFF013
  q23 : Eqn
  q23 = sE 122 lem-pass-X3-CSd31-X3-vs-CS02
  q24 : Eqn
  q24 = sE 123 lem-pass-X3-CSd31-X3-vs-CSd02

-- pass [X3 CSd31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CSd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (ℓ "丞举丞乞丧乞丨") ⟫ʷ ≈ ⟪ (ℓ "乞丧乞丨丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (ℓ "丞举丞乞丧乞丨") (ℓ "乞丧乞丨丞举丞")
  (rw 0 q22 ∷
   rw 1 q23 ∷
   rw 2 q22 ∷
   rw 3 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 145 lem-pass-X3-CSd32-X3-vs-CS01
  q26 : Eqn
  q26 = sE 149 lem-pass-X3-CSd32-X3-vs-TOFF023
  q27 : Eqn
  q27 = sE 147 lem-pass-X3-CSd32-X3-vs-CSd01

-- pass [X3 CSd32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (ℓ "丞乊丞丠也両也") ⟫ʷ ≈ ⟪ (ℓ "丠也両也丞乊丞") ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = derive (ℓ "丞乊丞丠也両也") (ℓ "丠也両也丞乊丞")
  (rw 0 q25 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 3 q26 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 139 lem-pass-X3-CKd32-X3-vs-CS01
  q29 : Eqn
  q29 = sE 141 lem-pass-X3-CKd32-X3-vs-TOFF023
  q30 : Eqn
  q30 = sE 140 lem-pass-X3-CKd32-X3-vs-CSd01

-- pass [X3 CKd32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (ℓ "丞乘丞丠也両也") ⟫ʷ ≈ ⟪ (ℓ "丠也両也丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = derive (ℓ "丞乘丞丠也両也") (ℓ "丠也両也丞乘丞")
  (rw 0 q28 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q29 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 142 lem-pass-X3-CS32-X3-vs-CS01
  q32 : Eqn
  q32 = sE 144 lem-pass-X3-CS32-X3-vs-TOFF023
  q33 : Eqn
  q33 = sE 143 lem-pass-X3-CS32-X3-vs-CSd01

-- pass [X3 CS32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (ℓ "丞义丞丠也両也") ⟫ʷ ≈ ⟪ (ℓ "丠也両也丞义丞") ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = derive (ℓ "丞义丞丠也両也") (ℓ "丠也両也丞义丞")
  (rw 0 q31 ∷
   rw 1 q32 ∷
   rw 2 q33 ∷
   rw 3 q32 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 164 lem-pass-TOFF201-vs-iI
  q35 : Eqn
  q35 = sE 161 lem-pass-CSd23-vs-iI
  q36 : Eqn
  q36 = sE 160 lem-pass-CS23-vs-iI

-- pass [CS23 TOFF201 CSd23 TOFF201] [iI]: 4 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI : ⟪ (ℓ "义乣乊乣一") ⟫ʷ ≈ ⟪ (ℓ "一义乣乊乣") ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI = derive (ℓ "义乣乊乣一") (ℓ "一义乣乊乣")
  (rw 3 q34 ∷
   rw 2 q35 ∷
   rw 1 q34 ∷
   rw 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 157 lem-pass-CS23-vs-Sd0
  q38 : Eqn
  q38 = wE 1383 W
  q39 : Eqn
  q39 = sE 162 lem-pass-Sd0-vs-CSd23

-- pass [Sd0] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "三义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣三") ⟫ʷ
lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "三义乣乊乣") (ℓ "义乣乊乣三")
  (rw⁻ 0 q37 ∷
   rw 1 q38 ∷
   rw 2 q39 ∷
   rw 3 q38 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 159 lem-pass-CS23-vs-Sd3
  q41 : Eqn
  q41 = eqn (ℓ "乣丛") (ℓ "丛乣") (low₃-comm (Toffᵗ) ((S • S • S)))
  q42 : Eqn
  q42 = sE 163 lem-pass-Sd3-vs-CSd23

-- pass [Sd3] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丛义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丛") ⟫ʷ
lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丛义乣乊乣") (ℓ "义乣乊乣丛")
  (rw⁻ 0 q40 ∷
   rw⁻ 1 q41 ∷
   rw 2 q42 ∷
   rw⁻ 3 q41 ∷ []) Eq.refl
