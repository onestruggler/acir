{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D315 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 464 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = wE 907 W
  q8 : Eqn
  q8 = wE 151 W
  q9 : Eqn
  q9 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q10 : Eqn
  q10 = eqn (ℓ "与之") (ℓ "之与") (low-comm ((S ↑)) (CZ))
  q11 : Eqn
  q11 = eqn (ℓ "临之") (ℓ "之临") (low-comm (CK₁₀) (CZ))
  q12 : Eqn
  q12 = wE 888 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q15 : Eqn
  q15 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = wE 890 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = wE 930 W
  q21 : Eqn
  q21 = wE 140 W
  q22 : Eqn
  q22 = wE 889 W
  q23 : Eqn
  q23 = wE 142 W
  q24 : Eqn
  q24 = wE 912 W

-- pass [CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [CZ23]: 660 steps
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CZ23 : ⟪ (ℓ "临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中之") ⟫ʷ ≈ ⟪ (ℓ "之临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CZ23 = derive (ℓ "临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中之") (ℓ "之临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中")
  (rw 74 q1 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q2 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q2 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q2 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q2 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q2 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q2 ∷
   rw 67 q3 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw 68 q2 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q2 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q2 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q2 ∷
   rw 62 q3 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 63 q2 ∷
   rw 60 q3 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 61 q2 ∷
   re 58 1 (ℓ "乏丹乏") ∷
   rw 60 q2 ∷
   rw 57 q3 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q2 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q2 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q2 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q2 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q2 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q2 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q2 ∷
   rw 38 q3 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q2 ∷
   rw 36 q3 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q2 ∷
   re 15 1 (ℓ "乏丹乏") ∷
   rw 17 q2 ∷
   rw 14 q4 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q4 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "乑") ∷
   rw 1 q8 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q8 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q8 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乓") ∷
   rw⁻ 16 q4 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q4 ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q4 ∷
   rw⁻ 32 q4 ∷
   rw⁻ 33 q4 ∷
   rw⁻ 34 q5 ∷
   rw⁻ 35 q5 ∷
   rw⁻ 36 q5 ∷
   rw⁻ 37 q6 ∷
   rw⁻ 38 q5 ∷
   rw⁻ 39 q4 ∷
   rw⁻ 40 q4 ∷
   rw⁻ 41 q4 ∷
   rw⁻ 42 q4 ∷
   rw⁻ 43 q4 ∷
   rw⁻ 44 q4 ∷
   rw⁻ 45 q4 ∷
   rw⁻ 46 q4 ∷
   rw⁻ 47 q4 ∷
   rw⁻ 48 q5 ∷
   rw⁻ 49 q5 ∷
   rw⁻ 50 q5 ∷
   rw⁻ 51 q6 ∷
   rw⁻ 52 q5 ∷
   rw⁻ 53 q5 ∷
   rw⁻ 54 q5 ∷
   rw⁻ 55 q5 ∷
   rw⁻ 56 q6 ∷
   rw⁻ 57 q5 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "乓") ∷
   rw⁻ 59 q6 ∷
   rw⁻ 60 q5 ∷
   rw⁻ 61 q6 ∷
   rw⁻ 62 q5 ∷
   rw⁻ 63 q4 ∷
   rw⁻ 64 q4 ∷
   rw⁻ 65 q4 ∷
   rw⁻ 66 q6 ∷
   rw⁻ 67 q5 ∷
   rw⁻ 68 q4 ∷
   rw⁻ 69 q4 ∷
   rw⁻ 70 q4 ∷
   rw⁻ 71 q4 ∷
   rw⁻ 72 q4 ∷
   rw⁻ 73 q4 ∷
   rw 74 q2 ∷
   rw 73 q9 ∷
   rw 72 q9 ∷
   rw 71 q9 ∷
   rw 70 q9 ∷
   rw 69 q9 ∷
   rw 68 q9 ∷
   rw 67 q10 ∷
   rw 66 q11 ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q9 ∷
   rw 62 q10 ∷
   rw 61 q11 ∷
   rw 60 q10 ∷
   rw 59 q11 ∷
   rw 58 q12 ∷
   rw 57 q10 ∷
   rw 56 q11 ∷
   rw 55 q10 ∷
   rw 54 q10 ∷
   rw 53 q10 ∷
   rw 52 q10 ∷
   rw 51 q11 ∷
   rw 50 q10 ∷
   rw 49 q10 ∷
   rw 48 q10 ∷
   rw 47 q9 ∷
   rw 46 q9 ∷
   rw 45 q9 ∷
   rw 44 q9 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw 36 q10 ∷
   rw 35 q10 ∷
   rw 34 q10 ∷
   rw 33 q9 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   rw 25 q9 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q9 ∷
   rw 15 q12 ∷
   rw 16 q13 ∷
   rw⁻ 15 q14 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q15 ∷
   rw 15 q16 ∷
   rw⁻ 14 q15 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q17 ∷
   rw 14 q14 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q15 ∷
   rw 16 q18 ∷
   rw 17 q15 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q19 ∷
   rw 15 q13 ∷
   rw⁻ 14 q14 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q15 ∷
   rw 14 q16 ∷
   rw⁻ 13 q15 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q17 ∷
   rw 13 q14 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q15 ∷
   rw 15 q18 ∷
   rw 16 q15 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q19 ∷
   rw 14 q13 ∷
   rw⁻ 13 q14 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q15 ∷
   rw 13 q16 ∷
   rw⁻ 12 q15 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q17 ∷
   rw 12 q14 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q15 ∷
   rw 14 q18 ∷
   rw 15 q15 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q19 ∷
   rw 13 q13 ∷
   rw⁻ 12 q14 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q15 ∷
   rw 12 q16 ∷
   rw⁻ 11 q15 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q17 ∷
   rw 11 q14 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q15 ∷
   rw 13 q18 ∷
   rw 14 q15 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q19 ∷
   rw 12 q13 ∷
   rw⁻ 11 q14 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q15 ∷
   rw 11 q16 ∷
   rw⁻ 10 q15 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q17 ∷
   rw 10 q14 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q15 ∷
   rw 12 q18 ∷
   rw 13 q15 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q19 ∷
   rw 11 q13 ∷
   rw⁻ 10 q14 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q15 ∷
   rw 10 q16 ∷
   rw⁻ 9 q15 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q17 ∷
   rw 9 q14 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q15 ∷
   rw 11 q18 ∷
   rw 12 q15 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q19 ∷
   rw 8 q20 ∷
   rw 9 q13 ∷
   rw⁻ 8 q14 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q15 ∷
   rw 8 q21 ∷
   rw⁻ 7 q15 ∷
   re 8 3 (ℓ "乔") ∷
   rw 8 q22 ∷
   rw 7 q14 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q15 ∷
   rw 9 q23 ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q19 ∷
   rw 8 q13 ∷
   rw⁻ 7 q14 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q15 ∷
   rw 7 q16 ∷
   rw⁻ 6 q15 ∷
   re 7 3 (ℓ "丽") ∷
   rw 7 q17 ∷
   rw 6 q14 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q15 ∷
   rw 8 q18 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q19 ∷
   rw 7 q13 ∷
   rw⁻ 6 q14 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q15 ∷
   rw 6 q16 ∷
   rw⁻ 5 q15 ∷
   re 6 3 (ℓ "丽") ∷
   rw 6 q17 ∷
   rw 5 q14 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q15 ∷
   rw 7 q18 ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q19 ∷
   rw 6 q13 ∷
   rw⁻ 5 q14 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q15 ∷
   rw 5 q16 ∷
   rw⁻ 4 q15 ∷
   re 5 3 (ℓ "丽") ∷
   rw 5 q17 ∷
   rw 4 q14 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q15 ∷
   rw 6 q18 ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q19 ∷
   rw 3 q20 ∷
   rw 4 q13 ∷
   rw⁻ 3 q14 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q15 ∷
   rw 3 q21 ∷
   rw⁻ 2 q15 ∷
   re 3 3 (ℓ "乔") ∷
   rw 3 q22 ∷
   rw 2 q14 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q15 ∷
   rw 4 q23 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "乑") ∷
   rw 4 q19 ∷
   rw 1 q20 ∷
   rw 2 q13 ∷
   rw⁻ 1 q14 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw⁻ 2 q15 ∷
   rw 1 q21 ∷
   rw⁻ 0 q15 ∷
   re 1 3 (ℓ "乔") ∷
   rw 1 q22 ∷
   rw 0 q14 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 1 q15 ∷
   rw 2 q23 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q19 ∷
   rw 75 q1 ∷
   rw 74 q4 ∷
   rw 73 q4 ∷
   rw 72 q4 ∷
   rw 71 q4 ∷
   rw 70 q4 ∷
   rw 69 q4 ∷
   rw 68 q5 ∷
   rw 67 q6 ∷
   rw 66 q4 ∷
   rw 65 q4 ∷
   rw 64 q4 ∷
   rw 63 q5 ∷
   rw 62 q6 ∷
   rw 61 q5 ∷
   rw 60 q6 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 61 q2 ∷
   rw 58 q5 ∷
   rw 57 q6 ∷
   rw 56 q5 ∷
   rw 55 q5 ∷
   rw 54 q5 ∷
   rw 53 q5 ∷
   rw 52 q6 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q4 ∷
   rw 39 q5 ∷
   rw 38 q6 ∷
   rw 37 q5 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q4 ∷
   rw 33 q4 ∷
   rw 32 q4 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 18 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q2 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q2 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q2 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q2 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   rw 4 q3 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q2 ∷
   rw 2 q3 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw 3 q2 ∷
   rw 2 q24 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 6 q4 ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q4 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乀") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q8 ∷
   rw 36 q8 ∷
   rw 37 q8 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q8 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q8 ∷
   rw 50 q8 ∷
   rw 51 q8 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q8 ∷
   rw 54 q8 ∷
   rw 55 q8 ∷
   rw 56 q8 ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乑") ∷
   rw 58 q8 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乀") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乑") ∷
   rw 61 q8 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q8 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q8 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q2 ∷ []) Eq.refl
