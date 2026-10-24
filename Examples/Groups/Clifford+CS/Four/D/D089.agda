{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D089 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 629 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 359 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q11 : Eqn
  q11 = wE 361 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (ℓ "乇业") (ℓ "业乇") (low₃-comm ((CK₁₀ ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q19 : Eqn
  q19 = wE 631 W

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [X2 CK21 X2] part0: 500 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CK21-X2-part0 : ⟪ (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中丘乇丘") ⟫ʷ ≈ ⟪ (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业丘乏丼临乗丼乏丘业乌乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CK21-X2-part0 = derive (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中丘乇丘") (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业丘乏丼临乗丼乏丘业乌乑业乑业中中中乑业中中中中中中")
  (rw 75 q1 ∷
   rw⁻ 74 q2 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q3 ∷
   rw 74 q4 ∷
   rw⁻ 73 q3 ∷
   re 74 3 (ℓ "丽") ∷
   rw 74 q5 ∷
   rw 73 q2 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q3 ∷
   rw 75 q6 ∷
   rw 76 q3 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q7 ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q8 ∷
   re 78 3 (ℓ "乔") ∷
   rw 77 q9 ∷
   rw 76 q10 ∷
   rw 75 q11 ∷
   re 75 1 (ℓ "乏乇乏") ∷
   rw 74 q12 ∷
   re 75 5 (ℓ "中") ∷
   rw 77 q1 ∷
   rw⁻ 76 q2 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q3 ∷
   rw 76 q4 ∷
   rw⁻ 75 q3 ∷
   re 76 3 (ℓ "丽") ∷
   rw 76 q5 ∷
   rw 75 q2 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q3 ∷
   rw 77 q6 ∷
   rw 78 q3 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q7 ∷
   rw 74 q1 ∷
   rw⁻ 73 q2 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q3 ∷
   rw 73 q4 ∷
   rw⁻ 72 q3 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q5 ∷
   rw 72 q2 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q3 ∷
   rw 74 q6 ∷
   rw 75 q3 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q7 ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q8 ∷
   re 77 3 (ℓ "乔") ∷
   rw 76 q9 ∷
   rw 75 q10 ∷
   rw 74 q11 ∷
   re 74 1 (ℓ "乏乇乏") ∷
   rw 73 q12 ∷
   re 74 5 (ℓ "中") ∷
   rw 76 q1 ∷
   rw⁻ 75 q2 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q3 ∷
   rw 75 q4 ∷
   rw⁻ 74 q3 ∷
   re 75 3 (ℓ "丽") ∷
   rw 75 q5 ∷
   rw 74 q2 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q3 ∷
   rw 76 q6 ∷
   rw 77 q3 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q7 ∷
   rw 73 q1 ∷
   rw⁻ 72 q2 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q3 ∷
   rw 72 q4 ∷
   rw⁻ 71 q3 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q5 ∷
   rw 71 q2 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q3 ∷
   rw 73 q6 ∷
   rw 74 q3 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q7 ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q8 ∷
   re 76 3 (ℓ "乔") ∷
   rw 75 q9 ∷
   rw 74 q10 ∷
   rw 73 q11 ∷
   re 73 1 (ℓ "乏乇乏") ∷
   rw 72 q12 ∷
   re 73 5 (ℓ "中") ∷
   rw 75 q1 ∷
   rw⁻ 74 q2 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q3 ∷
   rw 74 q4 ∷
   rw⁻ 73 q3 ∷
   re 74 3 (ℓ "丽") ∷
   rw 74 q5 ∷
   rw 73 q2 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q3 ∷
   rw 75 q6 ∷
   rw 76 q3 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q7 ∷
   rw 72 q1 ∷
   rw⁻ 71 q2 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q3 ∷
   rw 71 q4 ∷
   rw⁻ 70 q3 ∷
   re 71 3 (ℓ "丽") ∷
   rw 71 q5 ∷
   rw 70 q2 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q3 ∷
   rw 72 q6 ∷
   rw 73 q3 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q7 ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q8 ∷
   re 75 3 (ℓ "乔") ∷
   rw 74 q9 ∷
   rw 73 q10 ∷
   rw 72 q11 ∷
   re 72 1 (ℓ "乏乇乏") ∷
   rw 71 q12 ∷
   re 72 5 (ℓ "中") ∷
   rw 74 q1 ∷
   rw⁻ 73 q2 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q3 ∷
   rw 73 q4 ∷
   rw⁻ 72 q3 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q5 ∷
   rw 72 q2 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q3 ∷
   rw 74 q6 ∷
   rw 75 q3 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q7 ∷
   rw 71 q1 ∷
   rw⁻ 70 q2 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q3 ∷
   rw 70 q4 ∷
   rw⁻ 69 q3 ∷
   re 70 3 (ℓ "丽") ∷
   rw 70 q5 ∷
   rw 69 q2 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q3 ∷
   rw 71 q6 ∷
   rw 72 q3 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q7 ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q8 ∷
   re 74 3 (ℓ "乔") ∷
   rw 73 q9 ∷
   rw 72 q10 ∷
   rw 71 q11 ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q12 ∷
   re 71 5 (ℓ "中") ∷
   rw 73 q1 ∷
   rw⁻ 72 q2 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q3 ∷
   rw 72 q4 ∷
   rw⁻ 71 q3 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q5 ∷
   rw 71 q2 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q3 ∷
   rw 73 q6 ∷
   rw 74 q3 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q7 ∷
   rw 70 q1 ∷
   rw⁻ 69 q2 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q3 ∷
   rw 69 q4 ∷
   rw⁻ 68 q3 ∷
   re 69 3 (ℓ "丽") ∷
   rw 69 q5 ∷
   rw 68 q2 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q3 ∷
   rw 70 q6 ∷
   rw 71 q3 ∷
   re 69 3 (ℓ "中") ∷
   rw 70 q7 ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q8 ∷
   re 73 3 (ℓ "乔") ∷
   rw 72 q9 ∷
   rw 71 q10 ∷
   rw 70 q11 ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q12 ∷
   re 70 5 (ℓ "中") ∷
   rw 72 q1 ∷
   rw⁻ 71 q2 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q3 ∷
   rw 71 q4 ∷
   rw⁻ 70 q3 ∷
   re 71 3 (ℓ "丽") ∷
   rw 71 q5 ∷
   rw 70 q2 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q3 ∷
   rw 72 q6 ∷
   rw 73 q3 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q7 ∷
   rw⁻ 67 q13 ∷
   rw⁻ 68 q14 ∷
   rw⁻ 69 q13 ∷
   rw 68 q1 ∷
   rw⁻ 67 q2 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q3 ∷
   rw 67 q15 ∷
   rw⁻ 66 q3 ∷
   re 67 3 (ℓ "乔") ∷
   rw 67 q16 ∷
   rw 66 q2 ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q3 ∷
   rw 68 q17 ∷
   rw 69 q3 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q7 ∷
   re 67 1 (ℓ "乏丼临丼乏") ∷
   rw 73 q8 ∷
   re 71 3 (ℓ "乔") ∷
   rw 70 q9 ∷
   rw 69 q18 ∷
   rw 68 q11 ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q12 ∷
   re 68 5 (ℓ "乑") ∷
   rw 70 q1 ∷
   rw⁻ 69 q2 ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw⁻ 70 q3 ∷
   rw 69 q15 ∷
   rw⁻ 68 q3 ∷
   re 69 3 (ℓ "乔") ∷
   rw 69 q16 ∷
   rw 68 q2 ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q3 ∷
   rw 70 q17 ∷
   rw 71 q3 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q7 ∷
   rw 67 q1 ∷
   rw⁻ 66 q2 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q3 ∷
   rw 66 q4 ∷
   rw⁻ 65 q3 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q5 ∷
   rw 65 q2 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q3 ∷
   rw 67 q6 ∷
   rw 68 q3 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q7 ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q8 ∷
   re 70 3 (ℓ "乔") ∷
   rw 69 q9 ∷
   rw 68 q10 ∷
   rw 67 q11 ∷
   re 67 1 (ℓ "乏乇乏") ∷
   rw 66 q12 ∷
   re 67 5 (ℓ "中") ∷
   rw 69 q1 ∷
   rw⁻ 68 q2 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q3 ∷
   rw 68 q4 ∷
   rw⁻ 67 q3 ∷
   re 68 3 (ℓ "丽") ∷
   rw 68 q5 ∷
   rw 67 q2 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q3 ∷
   rw 69 q6 ∷
   rw 70 q3 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q7 ∷
   rw 66 q1 ∷
   rw⁻ 65 q2 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q3 ∷
   rw 65 q4 ∷
   rw⁻ 64 q3 ∷
   re 65 3 (ℓ "丽") ∷
   rw 65 q5 ∷
   rw 64 q2 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q3 ∷
   rw 66 q6 ∷
   rw 67 q3 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q7 ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q8 ∷
   re 69 3 (ℓ "乔") ∷
   rw 68 q9 ∷
   rw 67 q10 ∷
   rw 66 q11 ∷
   re 66 1 (ℓ "乏乇乏") ∷
   rw 65 q12 ∷
   re 66 5 (ℓ "中") ∷
   rw 68 q1 ∷
   rw⁻ 67 q2 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q3 ∷
   rw 67 q4 ∷
   rw⁻ 66 q3 ∷
   re 67 3 (ℓ "丽") ∷
   rw 67 q5 ∷
   rw 66 q2 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q3 ∷
   rw 68 q6 ∷
   rw 69 q3 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q7 ∷
   rw 65 q1 ∷
   rw⁻ 64 q2 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q3 ∷
   rw 64 q4 ∷
   rw⁻ 63 q3 ∷
   re 64 3 (ℓ "丽") ∷
   rw 64 q5 ∷
   rw 63 q2 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q3 ∷
   rw 65 q6 ∷
   rw 66 q3 ∷
   re 64 3 (ℓ "中") ∷
   rw 65 q7 ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q8 ∷
   re 68 3 (ℓ "乔") ∷
   rw 67 q9 ∷
   rw 66 q10 ∷
   rw 65 q11 ∷
   re 65 1 (ℓ "乏乇乏") ∷
   rw 64 q12 ∷
   re 65 5 (ℓ "中") ∷
   rw 67 q1 ∷
   rw⁻ 66 q2 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q3 ∷
   rw 66 q4 ∷
   rw⁻ 65 q3 ∷
   re 66 3 (ℓ "丽") ∷
   rw 66 q5 ∷
   rw 65 q2 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q3 ∷
   rw 67 q6 ∷
   rw 68 q3 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q7 ∷
   rw⁻ 62 q13 ∷
   rw⁻ 63 q14 ∷
   rw⁻ 64 q13 ∷
   rw 63 q1 ∷
   rw⁻ 62 q2 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw⁻ 63 q3 ∷
   rw 62 q15 ∷
   rw⁻ 61 q3 ∷
   re 62 3 (ℓ "乔") ∷
   rw 62 q16 ∷
   rw 61 q2 ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 62 q3 ∷
   rw 63 q17 ∷
   rw 64 q3 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q7 ∷
   re 62 1 (ℓ "乏丼临丼乏") ∷
   rw 68 q8 ∷
   re 66 3 (ℓ "乔") ∷
   rw 65 q9 ∷
   rw 64 q18 ∷
   rw 63 q11 ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 62 q12 ∷
   re 63 5 (ℓ "乑") ∷
   rw 65 q1 ∷
   rw⁻ 64 q2 ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw⁻ 65 q3 ∷
   rw 64 q15 ∷
   rw⁻ 63 q3 ∷
   re 64 3 (ℓ "乔") ∷
   rw 64 q16 ∷
   rw 63 q2 ∷
   re 65 1 (ℓ "乏乇乏") ∷
   rw 64 q3 ∷
   rw 65 q17 ∷
   rw 66 q3 ∷
   re 64 3 (ℓ "乑") ∷
   rw 65 q7 ∷
   rw⁻ 60 q13 ∷
   rw⁻ 61 q14 ∷
   rw⁻ 62 q13 ∷
   rw 61 q1 ∷
   rw⁻ 60 q2 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw⁻ 61 q3 ∷
   rw 60 q15 ∷
   rw⁻ 59 q3 ∷
   re 60 3 (ℓ "乔") ∷
   rw 60 q16 ∷
   rw 59 q2 ∷
   re 61 1 (ℓ "乏乇乏") ∷
   rw 60 q3 ∷
   rw 61 q17 ∷
   rw 62 q3 ∷
   re 60 3 (ℓ "乑") ∷
   rw 61 q7 ∷
   re 60 1 (ℓ "乏丼临丼乏") ∷
   rw 66 q8 ∷
   re 64 3 (ℓ "乔") ∷
   rw 63 q9 ∷
   rw 62 q18 ∷
   rw 61 q11 ∷
   re 61 1 (ℓ "乏乇乏") ∷
   rw 60 q12 ∷
   re 61 5 (ℓ "乑") ∷
   rw 63 q1 ∷
   rw⁻ 62 q2 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw⁻ 63 q3 ∷
   rw 62 q15 ∷
   rw⁻ 61 q3 ∷
   re 62 3 (ℓ "乔") ∷
   rw 62 q16 ∷
   rw 61 q2 ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 62 q3 ∷
   rw 63 q17 ∷
   rw 64 q3 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q7 ∷
   rw 58 q19 ∷
   rw⁻ 57 q13 ∷
   rw⁻ 58 q14 ∷
   rw⁻ 59 q13 ∷
   rw 58 q1 ∷
   rw⁻ 57 q2 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw⁻ 58 q3 ∷
   rw 57 q15 ∷
   rw⁻ 56 q3 ∷
   re 57 3 (ℓ "乔") ∷
   rw 57 q16 ∷
   rw 56 q2 ∷
   re 58 1 (ℓ "乏乇乏") ∷
   rw 57 q3 ∷
   rw 58 q17 ∷
   rw 59 q3 ∷
   re 57 3 (ℓ "乑") ∷
   rw 58 q7 ∷
   re 57 1 (ℓ "乏丼临丼乏") ∷
   rw 63 q8 ∷
   re 61 3 (ℓ "乔") ∷
   rw 60 q9 ∷ []) Eq.refl
