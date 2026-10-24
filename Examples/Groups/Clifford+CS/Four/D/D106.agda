{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D106 (W : Ws) where

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
  q1 = wE 360 W
  q2 : Eqn
  q2 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q3 : Eqn
  q3 = wE 362 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 629 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 1 W

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [X2 CKd21 X2] part2: 500 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CKd21-X2-part2 : ⟪ (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中丘乏丼丠丼乕乏丘业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中丘乏並丶乏並么丘中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CKd21-X2-part2 = derive (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中丘乏丼丠丼乕乏丘业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中") (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中丘乏並丶乏並么丘中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中")
  (rw 37 q1 ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   re 35 1 (ℓ "乏么乏") ∷
   rw 34 q4 ∷
   re 35 5 (ℓ "中") ∷
   rw 37 q5 ∷
   rw⁻ 36 q6 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q8 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q9 ∷
   rw 35 q6 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q7 ∷
   rw 37 q10 ∷
   rw 38 q7 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q11 ∷
   rw 34 q5 ∷
   rw⁻ 33 q6 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q7 ∷
   rw 33 q8 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q9 ∷
   rw 32 q6 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q7 ∷
   rw 34 q10 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q11 ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q12 ∷
   re 37 3 (ℓ "乕") ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   re 34 1 (ℓ "乏么乏") ∷
   rw 33 q4 ∷
   re 34 5 (ℓ "中") ∷
   rw 36 q5 ∷
   rw⁻ 35 q6 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q7 ∷
   rw 35 q8 ∷
   rw⁻ 34 q7 ∷
   re 35 3 (ℓ "丽") ∷
   rw 35 q9 ∷
   rw 34 q6 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q10 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q11 ∷
   rw 33 q5 ∷
   rw⁻ 32 q6 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q7 ∷
   rw 32 q8 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q9 ∷
   rw 31 q6 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q7 ∷
   rw 33 q10 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q11 ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q12 ∷
   re 36 3 (ℓ "乕") ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   re 33 1 (ℓ "乏么乏") ∷
   rw 32 q4 ∷
   re 33 5 (ℓ "中") ∷
   rw 35 q5 ∷
   rw⁻ 34 q6 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q7 ∷
   rw 34 q8 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (ℓ "丽") ∷
   rw 34 q9 ∷
   rw 33 q6 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q7 ∷
   rw 35 q10 ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q11 ∷
   rw 32 q5 ∷
   rw⁻ 31 q6 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q7 ∷
   rw 31 q8 ∷
   rw⁻ 30 q7 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q9 ∷
   rw 30 q6 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q7 ∷
   rw 32 q10 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q11 ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q12 ∷
   re 35 3 (ℓ "乕") ∷
   rw 34 q1 ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   re 32 1 (ℓ "乏么乏") ∷
   rw 31 q4 ∷
   re 32 5 (ℓ "中") ∷
   rw 34 q5 ∷
   rw⁻ 33 q6 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q7 ∷
   rw 33 q8 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q9 ∷
   rw 32 q6 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q7 ∷
   rw 34 q10 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q11 ∷
   rw 31 q5 ∷
   rw⁻ 30 q6 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q7 ∷
   rw 30 q8 ∷
   rw⁻ 29 q7 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q9 ∷
   rw 29 q6 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q7 ∷
   rw 31 q10 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q11 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q12 ∷
   re 34 3 (ℓ "乕") ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   re 31 1 (ℓ "乏么乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q5 ∷
   rw⁻ 32 q6 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q7 ∷
   rw 32 q8 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q9 ∷
   rw 31 q6 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q7 ∷
   rw 33 q10 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q11 ∷
   rw 30 q5 ∷
   rw⁻ 29 q6 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q7 ∷
   rw 29 q8 ∷
   rw⁻ 28 q7 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q9 ∷
   rw 28 q6 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q7 ∷
   rw 30 q10 ∷
   rw 31 q7 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q11 ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q12 ∷
   re 33 3 (ℓ "乕") ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   re 30 1 (ℓ "乏么乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "中") ∷
   rw 32 q5 ∷
   rw⁻ 31 q6 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q7 ∷
   rw 31 q8 ∷
   rw⁻ 30 q7 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q9 ∷
   rw 30 q6 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q7 ∷
   rw 32 q10 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q11 ∷
   rw 29 q5 ∷
   rw⁻ 28 q6 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q7 ∷
   rw 28 q8 ∷
   rw⁻ 27 q7 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q9 ∷
   rw 27 q6 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q7 ∷
   rw 29 q10 ∷
   rw 30 q7 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q11 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q12 ∷
   re 32 3 (ℓ "乕") ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   re 29 1 (ℓ "乏么乏") ∷
   rw 28 q4 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q5 ∷
   rw⁻ 30 q6 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q7 ∷
   rw 30 q8 ∷
   rw⁻ 29 q7 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q9 ∷
   rw 29 q6 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q7 ∷
   rw 31 q10 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q11 ∷
   rw 28 q5 ∷
   rw⁻ 27 q6 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q7 ∷
   rw 27 q8 ∷
   rw⁻ 26 q7 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q9 ∷
   rw 26 q6 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q7 ∷
   rw 28 q10 ∷
   rw 29 q7 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q11 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q12 ∷
   re 31 3 (ℓ "乕") ∷
   rw 30 q1 ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   re 28 1 (ℓ "乏么乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q5 ∷
   rw⁻ 29 q6 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q7 ∷
   rw 29 q8 ∷
   rw⁻ 28 q7 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q9 ∷
   rw 28 q6 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q7 ∷
   rw 30 q10 ∷
   rw 31 q7 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q11 ∷
   rw 27 q5 ∷
   rw⁻ 26 q6 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q7 ∷
   rw 26 q8 ∷
   rw⁻ 25 q7 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q9 ∷
   rw 25 q6 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q7 ∷
   rw 27 q10 ∷
   rw 28 q7 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q11 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q12 ∷
   re 30 3 (ℓ "乕") ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   re 27 1 (ℓ "乏么乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q5 ∷
   rw⁻ 28 q6 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q7 ∷
   rw 28 q8 ∷
   rw⁻ 27 q7 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q9 ∷
   rw 27 q6 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q7 ∷
   rw 29 q10 ∷
   rw 30 q7 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q11 ∷
   rw 26 q5 ∷
   rw⁻ 25 q6 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q7 ∷
   rw 25 q8 ∷
   rw⁻ 24 q7 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q9 ∷
   rw 24 q6 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q7 ∷
   rw 26 q10 ∷
   rw 27 q7 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q11 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q12 ∷
   re 29 3 (ℓ "乕") ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   re 26 1 (ℓ "乏么乏") ∷
   rw 25 q4 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q5 ∷
   rw⁻ 27 q6 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q7 ∷
   rw 27 q8 ∷
   rw⁻ 26 q7 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q9 ∷
   rw 26 q6 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q7 ∷
   rw 28 q10 ∷
   rw 29 q7 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q11 ∷
   rw 25 q5 ∷
   rw⁻ 24 q6 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q7 ∷
   rw 24 q8 ∷
   rw⁻ 23 q7 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q9 ∷
   rw 23 q6 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q7 ∷
   rw 25 q10 ∷
   rw 26 q7 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q11 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q12 ∷
   re 28 3 (ℓ "乕") ∷
   rw 27 q1 ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   re 25 1 (ℓ "乏么乏") ∷
   rw 24 q4 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q5 ∷
   rw⁻ 26 q6 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q7 ∷
   rw 26 q8 ∷
   rw⁻ 25 q7 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q9 ∷
   rw 25 q6 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q7 ∷
   rw 27 q10 ∷
   rw 28 q7 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q11 ∷
   rw 24 q5 ∷
   rw⁻ 23 q6 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q7 ∷
   rw 23 q8 ∷
   rw⁻ 22 q7 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q9 ∷
   rw 22 q6 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q7 ∷
   rw 24 q10 ∷
   rw 25 q7 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q11 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q12 ∷
   re 27 3 (ℓ "乕") ∷
   rw 26 q1 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   re 24 1 (ℓ "乏么乏") ∷
   rw 23 q4 ∷
   re 24 5 (ℓ "中") ∷
   rw 26 q5 ∷
   rw⁻ 25 q6 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q7 ∷
   rw 25 q8 ∷
   rw⁻ 24 q7 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q9 ∷
   rw 24 q6 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q7 ∷
   rw 26 q10 ∷
   rw 27 q7 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q11 ∷
   rw 23 q5 ∷
   rw⁻ 22 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q7 ∷
   rw 22 q8 ∷
   rw⁻ 21 q7 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q9 ∷
   rw 21 q6 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q7 ∷
   rw 23 q10 ∷
   rw 24 q7 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q11 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q12 ∷
   re 26 3 (ℓ "乕") ∷
   rw 25 q1 ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   re 23 1 (ℓ "乏么乏") ∷
   rw 22 q4 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q5 ∷
   rw⁻ 24 q6 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q7 ∷
   rw 24 q8 ∷
   rw⁻ 23 q7 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q9 ∷
   rw 23 q6 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q7 ∷
   rw 25 q10 ∷
   rw 26 q7 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q11 ∷
   rw 22 q5 ∷
   rw⁻ 21 q6 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q7 ∷
   rw 21 q8 ∷
   rw⁻ 20 q7 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q9 ∷
   rw 20 q6 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q7 ∷ []) Eq.refl
