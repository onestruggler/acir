{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D308 (W : Ws) where

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
  q7 = wE 929 W
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
  q24 = wE 931 W

-- pass [CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03] [CZ23]: 824 steps
lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-CZ23 : ⟪ (ℓ "丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中之") ⟫ʷ ≈ ⟪ (ℓ "之丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-CZ23 = derive (ℓ "丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中之") (ℓ "之丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中")
  (rw 86 q1 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q2 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q2 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q2 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q2 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q2 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q2 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q2 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q2 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q2 ∷
   rw 76 q3 ∷
   re 75 1 (ℓ "乏乄乏") ∷
   rw 77 q2 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q2 ∷
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
   re 68 1 (ℓ "乏丹乏") ∷
   rw 70 q2 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q2 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q2 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q2 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q2 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q2 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q2 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q2 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q2 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q2 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q2 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q2 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q2 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q2 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q2 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q2 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q2 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q2 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q2 ∷
   rw 49 q3 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw 50 q2 ∷
   rw 47 q3 ∷
   rw 46 q3 ∷
   rw 45 q3 ∷
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
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q2 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q2 ∷
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
   re 17 1 (ℓ "乏丹乏") ∷
   rw 19 q2 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw 14 q4 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q4 ∷
   rw 2 q4 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q7 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q8 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
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
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乓") ∷
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
   rw⁻ 34 q4 ∷
   rw⁻ 35 q4 ∷
   rw⁻ 36 q4 ∷
   rw⁻ 37 q4 ∷
   rw⁻ 38 q4 ∷
   rw⁻ 39 q4 ∷
   rw⁻ 40 q4 ∷
   rw⁻ 41 q4 ∷
   rw⁻ 42 q4 ∷
   rw⁻ 43 q4 ∷
   rw⁻ 44 q4 ∷
   rw⁻ 45 q5 ∷
   rw⁻ 46 q5 ∷
   rw⁻ 47 q5 ∷
   rw⁻ 48 q6 ∷
   rw⁻ 49 q5 ∷
   rw⁻ 50 q4 ∷
   rw⁻ 51 q4 ∷
   rw⁻ 52 q4 ∷
   rw⁻ 53 q4 ∷
   rw⁻ 54 q4 ∷
   rw⁻ 55 q4 ∷
   rw⁻ 56 q4 ∷
   rw⁻ 57 q4 ∷
   rw⁻ 58 q4 ∷
   rw⁻ 59 q4 ∷
   rw⁻ 60 q4 ∷
   rw⁻ 61 q4 ∷
   rw⁻ 62 q4 ∷
   rw⁻ 63 q4 ∷
   rw⁻ 64 q4 ∷
   rw⁻ 65 q4 ∷
   rw⁻ 66 q4 ∷
   rw⁻ 67 q4 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "乓") ∷
   rw⁻ 69 q4 ∷
   rw⁻ 70 q4 ∷
   rw⁻ 71 q4 ∷
   rw⁻ 72 q4 ∷
   rw⁻ 73 q4 ∷
   rw⁻ 74 q4 ∷
   rw⁻ 75 q6 ∷
   rw⁻ 76 q5 ∷
   rw⁻ 77 q4 ∷
   rw⁻ 78 q4 ∷
   rw⁻ 79 q4 ∷
   rw⁻ 80 q4 ∷
   rw⁻ 81 q4 ∷
   rw⁻ 82 q4 ∷
   rw⁻ 83 q4 ∷
   rw⁻ 84 q4 ∷
   rw⁻ 85 q4 ∷
   rw 86 q2 ∷
   rw 85 q9 ∷
   rw 84 q9 ∷
   rw 83 q9 ∷
   rw 82 q9 ∷
   rw 81 q9 ∷
   rw 80 q9 ∷
   rw 79 q9 ∷
   rw 78 q9 ∷
   rw 77 q9 ∷
   rw 76 q10 ∷
   rw 75 q11 ∷
   rw 74 q9 ∷
   rw 73 q9 ∷
   rw 72 q9 ∷
   rw 71 q9 ∷
   rw 70 q9 ∷
   rw 69 q9 ∷
   rw 68 q12 ∷
   rw 67 q9 ∷
   rw 66 q9 ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q9 ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q10 ∷
   rw 48 q11 ∷
   rw 47 q10 ∷
   rw 46 q10 ∷
   rw 45 q10 ∷
   rw 44 q9 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q9 ∷
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
   rw 17 q12 ∷
   rw 18 q13 ∷
   rw⁻ 17 q14 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q15 ∷
   rw 17 q16 ∷
   rw⁻ 16 q15 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q17 ∷
   rw 16 q14 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q15 ∷
   rw 18 q18 ∷
   rw 19 q15 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q19 ∷
   rw 17 q13 ∷
   rw⁻ 16 q14 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q15 ∷
   rw 16 q16 ∷
   rw⁻ 15 q15 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q17 ∷
   rw 15 q14 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q15 ∷
   rw 17 q18 ∷
   rw 18 q15 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q19 ∷
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
   rw 10 q13 ∷
   rw⁻ 9 q14 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q15 ∷
   rw 9 q16 ∷
   rw⁻ 8 q15 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q17 ∷
   rw 8 q14 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q15 ∷
   rw 10 q18 ∷
   rw 11 q15 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q19 ∷
   rw 7 q20 ∷
   rw 8 q13 ∷
   rw⁻ 7 q14 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw⁻ 8 q15 ∷
   rw 7 q21 ∷
   rw⁻ 6 q15 ∷
   re 7 3 (ℓ "乔") ∷
   rw 7 q22 ∷
   rw 6 q14 ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q15 ∷
   rw 8 q23 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "乑") ∷
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
   rw 5 q13 ∷
   rw⁻ 4 q14 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q15 ∷
   rw 4 q16 ∷
   rw⁻ 3 q15 ∷
   re 4 3 (ℓ "丽") ∷
   rw 4 q17 ∷
   rw 3 q14 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q15 ∷
   rw 5 q18 ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q19 ∷
   rw 4 q13 ∷
   rw⁻ 3 q14 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q15 ∷
   rw 3 q16 ∷
   rw⁻ 2 q15 ∷
   re 3 3 (ℓ "丽") ∷
   rw 3 q17 ∷
   rw 2 q14 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q15 ∷
   rw 4 q18 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q19 ∷
   rw 3 q13 ∷
   rw⁻ 2 q14 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q15 ∷
   rw 2 q16 ∷
   rw⁻ 1 q15 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q17 ∷
   rw 1 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q15 ∷
   rw 3 q18 ∷
   rw 4 q15 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q19 ∷
   rw 2 q13 ∷
   rw⁻ 1 q14 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q15 ∷
   rw 1 q16 ∷
   rw⁻ 0 q15 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q17 ∷
   rw 0 q14 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q15 ∷
   rw 2 q18 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q19 ∷
   rw 87 q1 ∷
   rw 86 q4 ∷
   rw 85 q4 ∷
   rw 84 q4 ∷
   rw 83 q4 ∷
   rw 82 q4 ∷
   rw 81 q4 ∷
   rw 80 q4 ∷
   rw 79 q4 ∷
   rw 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q6 ∷
   rw 75 q4 ∷
   rw 74 q4 ∷
   rw 73 q4 ∷
   rw 72 q4 ∷
   rw 71 q4 ∷
   rw 70 q4 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 71 q2 ∷
   rw 68 q4 ∷
   rw 67 q4 ∷
   rw 66 q4 ∷
   rw 65 q4 ∷
   rw 64 q4 ∷
   rw 63 q4 ∷
   rw 62 q4 ∷
   rw 61 q4 ∷
   rw 60 q4 ∷
   rw 59 q4 ∷
   rw 58 q4 ∷
   rw 57 q4 ∷
   rw 56 q4 ∷
   rw 55 q4 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   rw 52 q4 ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   rw 49 q6 ∷
   rw 48 q5 ∷
   rw 47 q5 ∷
   rw 46 q5 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q4 ∷
   rw 39 q4 ∷
   rw 38 q4 ∷
   rw 37 q4 ∷
   rw 36 q4 ∷
   rw 35 q4 ∷
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
   re 18 1 (ℓ "乏乆乏") ∷
   rw 20 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
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
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q2 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q2 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q2 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q2 ∷
   rw 2 q24 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q4 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 6 q4 ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q4 ∷
   rw⁻ 17 q4 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乀") ∷
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
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
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
   rw 46 q8 ∷
   rw 47 q8 ∷
   rw 48 q8 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q8 ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乀") ∷
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
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "乑") ∷
   rw 77 q8 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   rw 87 q2 ∷ []) Eq.refl
