{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD517 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D517 (W : Ws) (Sᴰ : SD517) where

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
  lem-pass-CS13-vs-CS02 : St 27
  lem-pass-CS13-vs-CS02 = pickᴰ 0 Sᴰ
  lem-pass-CSd02-vs-CS13 : St 28
  lem-pass-CSd02-vs-CS13 = pickᴰ 1 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS12 : St 42
  lem-pass-X3-CK30-X3-vs-CS12 = pickᴰ 2 Sᴰ
  lem-pass-X3-CK30-X3-vs-CSd12 : St 43
  lem-pass-X3-CK30-X3-vs-CSd12 = pickᴰ 3 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF103 : St 44
  lem-pass-X3-CK30-X3-vs-TOFF103 = pickᴰ 4 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS12 : St 45
  lem-pass-X3-CKd30-X3-vs-CS12 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CSd12 : St 46
  lem-pass-X3-CKd30-X3-vs-CSd12 = pickᴰ 6 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF103 : St 47
  lem-pass-X3-CKd30-X3-vs-TOFF103 = pickᴰ 7 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS12 : St 48
  lem-pass-X3-CS30-X3-vs-CS12 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS30-X3-vs-CSd12 : St 49
  lem-pass-X3-CS30-X3-vs-CSd12 = pickᴰ 9 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF103 : St 50
  lem-pass-X3-CS30-X3-vs-TOFF103 = pickᴰ 10 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS12 : St 51
  lem-pass-X3-CSd30-X3-vs-CS12 = pickᴰ 11 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CSd12 : St 52
  lem-pass-X3-CSd30-X3-vs-CSd12 = pickᴰ 12 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF103 : St 53
  lem-pass-X3-CSd30-X3-vs-TOFF103 = pickᴰ 13 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS13 : St 69
  lem-pass-X2-CK20-X2-vs-CS13 = pickᴰ 14 Sᴰ
  lem-pass-X2-CK20-X2-vs-CSd13 : St 70
  lem-pass-X2-CK20-X2-vs-CSd13 = pickᴰ 15 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF102 : St 71
  lem-pass-X2-CK20-X2-vs-TOFF102 = pickᴰ 16 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS13 : St 72
  lem-pass-X2-CKd20-X2-vs-CS13 = pickᴰ 17 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CSd13 : St 73
  lem-pass-X2-CKd20-X2-vs-CSd13 = pickᴰ 18 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF102 : St 74
  lem-pass-X2-CKd20-X2-vs-TOFF102 = pickᴰ 19 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS13 : St 76
  lem-pass-X2-CS20-X2-vs-CS13 = pickᴰ 20 Sᴰ
  lem-pass-X2-CS20-X2-vs-CSd13 : St 78
  lem-pass-X2-CS20-X2-vs-CSd13 = pickᴰ 21 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF102 : St 80
  lem-pass-X2-CS20-X2-vs-TOFF102 = pickᴰ 22 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS13 : St 81
  lem-pass-X2-CSd20-X2-vs-CS13 = pickᴰ 23 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CSd13 : St 82
  lem-pass-X2-CSd20-X2-vs-CSd13 = pickᴰ 24 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF102 : St 83
  lem-pass-X2-CSd20-X2-vs-TOFF102 = pickᴰ 25 Sᴰ
  lem-comm-CCZ012-CSd23 : St 171
  lem-comm-CCZ012-CSd23 = pickᴰ 26 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03 : St 172
  lem-pass-X1-CSd10-X1-vs-CS03 = pickᴰ 27 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CSd03 : St 173
  lem-pass-X1-CSd10-X1-vs-CSd03 = pickᴰ 28 Sᴰ
  lem-pass-X1-CSd10-X1-vs-TOFF012 : St 174
  lem-pass-X1-CSd10-X1-vs-TOFF012 = pickᴰ 29 Sᴰ

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
  q14 = sE 27 lem-pass-CS13-vs-CS02
  q15 : Eqn
  q15 = sE 28 lem-pass-CSd02-vs-CS13

-- pass [CS13] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 382 steps
lem-pass-CS13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (ℓ "丽丞乞丞丧丞乞丞丨") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞丧丞乞丞丨丽") ⟫ʷ
lem-pass-CS13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (ℓ "丽丞乞丞丧丞乞丞丨") (ℓ "丞乞丞丧丞乞丞丨丽")
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
   rw 3 q14 ∷
   rw 8 q1 ∷
   rw 7 q2 ∷
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
   rw 5 q2 ∷
   rw 6 q8 ∷
   rw⁻ 5 q9 ∷
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
   rw 7 q6 ∷
   rw 6 q1 ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 5 q10 ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q6 ∷
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
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 6 q11 ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 5 q1 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "九") ∷
   re 5 3 (ℓ "乞") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q6 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏九乏") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "九") ∷
   rw 4 q9 ∷
   rw 5 q12 ∷
   rw 4 q13 ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 5 q1 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q7 ∷
   re 6 8 (ℓ "九") ∷
   re 5 3 (ℓ "乞") ∷
   rw 6 q13 ∷
   rw 7 q6 ∷
   rw⁻ 7 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 51 lem-pass-X3-CSd30-X3-vs-CS12
  q17 : Eqn
  q17 = sE 53 lem-pass-X3-CSd30-X3-vs-TOFF103
  q18 : Eqn
  q18 = sE 52 lem-pass-X3-CSd30-X3-vs-CSd12

-- pass [X3 CSd30 X3] [CS12 TOFF103 CSd12 TOFF103]: 4 steps
lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : ⟪ (ℓ "丞丮丞丶乡丷乡") ⟫ʷ ≈ ⟪ (ℓ "丶乡丷乡丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = derive (ℓ "丞丮丞丶乡丷乡") (ℓ "丶乡丷乡丞丮丞")
  (rw 0 q16 ∷
   rw 1 q17 ∷
   rw 2 q18 ∷
   rw 3 q17 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 45 lem-pass-X3-CKd30-X3-vs-CS12
  q20 : Eqn
  q20 = sE 47 lem-pass-X3-CKd30-X3-vs-TOFF103
  q21 : Eqn
  q21 = sE 46 lem-pass-X3-CKd30-X3-vs-CSd12

-- pass [X3 CKd30 X3] [CS12 TOFF103 CSd12 TOFF103]: 4 steps
lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : ⟪ (ℓ "丞乒丞丶乡丷乡") ⟫ʷ ≈ ⟪ (ℓ "丶乡丷乡丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = derive (ℓ "丞乒丞丶乡丷乡") (ℓ "丶乡丷乡丞乒丞")
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 2 q21 ∷
   rw 3 q20 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = sE 42 lem-pass-X3-CK30-X3-vs-CS12
  q23 : Eqn
  q23 = sE 44 lem-pass-X3-CK30-X3-vs-TOFF103
  q24 : Eqn
  q24 = sE 43 lem-pass-X3-CK30-X3-vs-CSd12

-- pass [X3 CK30 X3] [CS12 TOFF103 CSd12 TOFF103]: 4 steps
lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : ⟪ (ℓ "丞乑丞丶乡丷乡") ⟫ʷ ≈ ⟪ (ℓ "丶乡丷乡丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = derive (ℓ "丞乑丞丶乡丷乡") (ℓ "丶乡丷乡丞乑丞")
  (rw 0 q22 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 3 q23 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 48 lem-pass-X3-CS30-X3-vs-CS12
  q26 : Eqn
  q26 = sE 50 lem-pass-X3-CS30-X3-vs-TOFF103
  q27 : Eqn
  q27 = sE 49 lem-pass-X3-CS30-X3-vs-CSd12

-- pass [X3 CS30 X3] [CS12 TOFF103 CSd12 TOFF103]: 4 steps
lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103 : ⟪ (ℓ "丞中丞丶乡丷乡") ⟫ʷ ≈ ⟪ (ℓ "丶乡丷乡丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS12-TOFF103-CSd12-TOFF103 = derive (ℓ "丞中丞丶乡丷乡") (ℓ "丶乡丷乡丞中丞")
  (rw 0 q25 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 3 q26 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 81 lem-pass-X2-CSd20-X2-vs-CS13
  q29 : Eqn
  q29 = sE 83 lem-pass-X2-CSd20-X2-vs-TOFF102
  q30 : Eqn
  q30 = sE 82 lem-pass-X2-CSd20-X2-vs-CSd13

-- pass [X2 CSd20 X2] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘丨丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘丨丘丽习举习") (ℓ "丽习举习丘丨丘")
  (rw 0 q28 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q29 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 72 lem-pass-X2-CKd20-X2-vs-CS13
  q32 : Eqn
  q32 = sE 74 lem-pass-X2-CKd20-X2-vs-TOFF102
  q33 : Eqn
  q33 = sE 73 lem-pass-X2-CKd20-X2-vs-CSd13

-- pass [X2 CKd20 X2] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘久丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘久丘丽习举习") (ℓ "丽习举习丘久丘")
  (rw 0 q31 ∷
   rw 1 q32 ∷
   rw 2 q33 ∷
   rw 3 q32 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 69 lem-pass-X2-CK20-X2-vs-CS13
  q35 : Eqn
  q35 = sE 71 lem-pass-X2-CK20-X2-vs-TOFF102
  q36 : Eqn
  q36 = sE 70 lem-pass-X2-CK20-X2-vs-CSd13

-- pass [X2 CK20 X2] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘乄丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘乄丘丽习举习") (ℓ "丽习举习丘乄丘")
  (rw 0 q34 ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw 3 q35 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 76 lem-pass-X2-CS20-X2-vs-CS13
  q38 : Eqn
  q38 = sE 80 lem-pass-X2-CS20-X2-vs-TOFF102
  q39 : Eqn
  q39 = sE 78 lem-pass-X2-CS20-X2-vs-CSd13

-- pass [X2 CS20 X2] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘丧丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘丧丘丽习举习") (ℓ "丽习举习丘丧丘")
  (rw 0 q37 ∷
   rw 1 q38 ∷
   rw 2 q39 ∷
   rw 3 q38 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 174 lem-pass-X1-CSd10-X1-vs-TOFF012
  q41 : Eqn
  q41 = sE 172 lem-pass-X1-CSd10-X1-vs-CS03
  q42 : Eqn
  q42 = sE 173 lem-pass-X1-CSd10-X1-vs-CSd03

-- pass [X1 CSd10 X1] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丒両丒九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丒両丒九中九丮") (ℓ "九中九丮丒両丒")
  (rw 0 q40 ∷
   rw 1 q41 ∷
   rw 2 q40 ∷
   rw 3 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 171 lem-comm-CCZ012-CSd23

-- pass [CCZ012] [CSd23]: 1 steps
lem-pass-CCZ012-vs-CSd23 : ⟪ (ℓ "乙乊") ⟫ʷ ≈ ⟪ (ℓ "乊乙") ⟫ʷ
lem-pass-CCZ012-vs-CSd23 = derive (ℓ "乙乊") (ℓ "乊乙")
  (rw 0 q43 ∷ []) Eq.refl
