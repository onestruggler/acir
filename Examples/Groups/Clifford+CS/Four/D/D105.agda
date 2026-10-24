{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D105 (W : Ws) where

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
  q1 = eqn (ℓ "临乘") (ℓ "乘临") (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q2 : Eqn
  q2 = wE 362 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 140 W
  q8 : Eqn
  q8 = wE 630 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q12 : Eqn
  q12 = eqn (ℓ "么业") (ℓ "业么") (low₃-comm (((S ↑ • CK₁₀) ↑)) (S))
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 360 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 629 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [X2 CKd21 X2] part1: 500 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CKd21-X2-part1 : ⟪ (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业丘乏丼临乘丼乏丘业乌乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中丘乏丼丠丼乕乏丘业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CKd21-X2-part1 = derive (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业丘乏丼临乘丼乏丘业乌乑业乑业中中中乑业中中中中中中") (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中丘乏丼丠丼乕乏丘业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中")
  (rw 59 q1 ∷
   rw 58 q2 ∷
   re 58 1 (ℓ "乏么乏") ∷
   rw 57 q3 ∷
   re 58 5 (ℓ "乑") ∷
   rw 60 q4 ∷
   rw⁻ 59 q5 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw⁻ 60 q6 ∷
   rw 59 q7 ∷
   rw⁻ 58 q6 ∷
   re 59 3 (ℓ "乔") ∷
   rw 59 q8 ∷
   rw 58 q5 ∷
   re 60 1 (ℓ "乏乇乏") ∷
   rw 59 q6 ∷
   rw 60 q9 ∷
   rw 61 q6 ∷
   re 59 3 (ℓ "乑") ∷
   rw 60 q10 ∷
   rw⁻ 55 q11 ∷
   rw⁻ 56 q12 ∷
   rw⁻ 57 q11 ∷
   rw⁻ 54 q11 ∷
   rw⁻ 55 q12 ∷
   rw⁻ 56 q11 ∷
   rw⁻ 53 q11 ∷
   rw⁻ 54 q12 ∷
   rw⁻ 55 q11 ∷
   rw⁻ 52 q11 ∷
   rw⁻ 53 q12 ∷
   rw⁻ 54 q11 ∷
   rw 53 q4 ∷
   rw⁻ 52 q5 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw⁻ 53 q6 ∷
   rw 52 q7 ∷
   rw⁻ 51 q6 ∷
   re 52 3 (ℓ "乔") ∷
   rw 52 q8 ∷
   rw 51 q5 ∷
   re 53 1 (ℓ "乏乇乏") ∷
   rw 52 q6 ∷
   rw 53 q9 ∷
   rw 54 q6 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q10 ∷
   re 52 1 (ℓ "乏丼临丼乏") ∷
   rw 58 q13 ∷
   re 56 3 (ℓ "乕") ∷
   rw 55 q14 ∷
   rw 54 q1 ∷
   rw 53 q2 ∷
   re 53 1 (ℓ "乏么乏") ∷
   rw 52 q3 ∷
   re 53 5 (ℓ "乑") ∷
   rw 55 q4 ∷
   rw⁻ 54 q5 ∷
   re 53 1 (ℓ "乏乄乏") ∷
   rw⁻ 55 q6 ∷
   rw 54 q7 ∷
   rw⁻ 53 q6 ∷
   re 54 3 (ℓ "乔") ∷
   rw 54 q8 ∷
   rw 53 q5 ∷
   re 55 1 (ℓ "乏乇乏") ∷
   rw 54 q6 ∷
   rw 55 q9 ∷
   rw 56 q6 ∷
   re 54 3 (ℓ "乑") ∷
   rw 55 q10 ∷
   rw⁻ 50 q11 ∷
   rw⁻ 51 q12 ∷
   rw⁻ 52 q11 ∷
   rw⁻ 49 q11 ∷
   rw⁻ 50 q12 ∷
   rw⁻ 51 q11 ∷
   rw⁻ 48 q11 ∷
   rw⁻ 49 q12 ∷
   rw⁻ 50 q11 ∷
   rw 49 q4 ∷
   rw⁻ 48 q5 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q6 ∷
   rw 48 q15 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q16 ∷
   rw 47 q5 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q6 ∷
   rw 49 q17 ∷
   rw 50 q6 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q10 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q13 ∷
   re 52 3 (ℓ "乕") ∷
   rw 51 q14 ∷
   rw 50 q18 ∷
   rw 49 q2 ∷
   re 49 1 (ℓ "乏么乏") ∷
   rw 48 q3 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q4 ∷
   rw⁻ 50 q5 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q6 ∷
   rw 50 q15 ∷
   rw⁻ 49 q6 ∷
   re 50 3 (ℓ "丽") ∷
   rw 50 q16 ∷
   rw 49 q5 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q6 ∷
   rw 51 q17 ∷
   rw 52 q6 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q10 ∷
   rw 48 q4 ∷
   rw⁻ 47 q5 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q6 ∷
   rw 47 q15 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q16 ∷
   rw 46 q5 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q6 ∷
   rw 48 q17 ∷
   rw 49 q6 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q10 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q13 ∷
   re 51 3 (ℓ "乕") ∷
   rw 50 q14 ∷
   rw 49 q18 ∷
   rw 48 q2 ∷
   re 48 1 (ℓ "乏么乏") ∷
   rw 47 q3 ∷
   re 48 5 (ℓ "中") ∷
   rw 50 q4 ∷
   rw⁻ 49 q5 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q6 ∷
   rw 49 q15 ∷
   rw⁻ 48 q6 ∷
   re 49 3 (ℓ "丽") ∷
   rw 49 q16 ∷
   rw 48 q5 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q6 ∷
   rw 50 q17 ∷
   rw 51 q6 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q10 ∷
   rw 47 q4 ∷
   rw⁻ 46 q5 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q6 ∷
   rw 46 q15 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q16 ∷
   rw 45 q5 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q6 ∷
   rw 47 q17 ∷
   rw 48 q6 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q10 ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q13 ∷
   re 50 3 (ℓ "乕") ∷
   rw 49 q14 ∷
   rw 48 q18 ∷
   rw 47 q2 ∷
   re 47 1 (ℓ "乏么乏") ∷
   rw 46 q3 ∷
   re 47 5 (ℓ "中") ∷
   rw 49 q4 ∷
   rw⁻ 48 q5 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q6 ∷
   rw 48 q15 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q16 ∷
   rw 47 q5 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q6 ∷
   rw 49 q17 ∷
   rw 50 q6 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q10 ∷
   rw 46 q4 ∷
   rw⁻ 45 q5 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q6 ∷
   rw 45 q15 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q16 ∷
   rw 44 q5 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q6 ∷
   rw 46 q17 ∷
   rw 47 q6 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q10 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q13 ∷
   re 49 3 (ℓ "乕") ∷
   rw 48 q14 ∷
   rw 47 q18 ∷
   rw 46 q2 ∷
   re 46 1 (ℓ "乏么乏") ∷
   rw 45 q3 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q4 ∷
   rw⁻ 47 q5 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q6 ∷
   rw 47 q15 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q16 ∷
   rw 46 q5 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q6 ∷
   rw 48 q17 ∷
   rw 49 q6 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q10 ∷
   rw 45 q4 ∷
   rw⁻ 44 q5 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q6 ∷
   rw 44 q15 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q16 ∷
   rw 43 q5 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q6 ∷
   rw 45 q17 ∷
   rw 46 q6 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q10 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q13 ∷
   re 48 3 (ℓ "乕") ∷
   rw 47 q14 ∷
   rw 46 q18 ∷
   rw 45 q2 ∷
   re 45 1 (ℓ "乏么乏") ∷
   rw 44 q3 ∷
   re 45 5 (ℓ "中") ∷
   rw 47 q4 ∷
   rw⁻ 46 q5 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q6 ∷
   rw 46 q15 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q16 ∷
   rw 45 q5 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q6 ∷
   rw 47 q17 ∷
   rw 48 q6 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q10 ∷
   rw 44 q4 ∷
   rw⁻ 43 q5 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q6 ∷
   rw 43 q15 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q16 ∷
   rw 42 q5 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q6 ∷
   rw 44 q17 ∷
   rw 45 q6 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q10 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q13 ∷
   re 47 3 (ℓ "乕") ∷
   rw 46 q14 ∷
   rw 45 q18 ∷
   rw 44 q2 ∷
   re 44 1 (ℓ "乏么乏") ∷
   rw 43 q3 ∷
   re 44 5 (ℓ "中") ∷
   rw 46 q4 ∷
   rw⁻ 45 q5 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q6 ∷
   rw 45 q15 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q16 ∷
   rw 44 q5 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q6 ∷
   rw 46 q17 ∷
   rw 47 q6 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q10 ∷
   rw 43 q4 ∷
   rw⁻ 42 q5 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q6 ∷
   rw 42 q15 ∷
   rw⁻ 41 q6 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q16 ∷
   rw 41 q5 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q6 ∷
   rw 43 q17 ∷
   rw 44 q6 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q10 ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q13 ∷
   re 46 3 (ℓ "乕") ∷
   rw 45 q14 ∷
   rw 44 q18 ∷
   rw 43 q2 ∷
   re 43 1 (ℓ "乏么乏") ∷
   rw 42 q3 ∷
   re 43 5 (ℓ "中") ∷
   rw 45 q4 ∷
   rw⁻ 44 q5 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q6 ∷
   rw 44 q15 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q16 ∷
   rw 43 q5 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q6 ∷
   rw 45 q17 ∷
   rw 46 q6 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q10 ∷
   rw 42 q4 ∷
   rw⁻ 41 q5 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q6 ∷
   rw 41 q15 ∷
   rw⁻ 40 q6 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q16 ∷
   rw 40 q5 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q6 ∷
   rw 42 q17 ∷
   rw 43 q6 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q10 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q13 ∷
   re 45 3 (ℓ "乕") ∷
   rw 44 q14 ∷
   rw 43 q18 ∷
   rw 42 q2 ∷
   re 42 1 (ℓ "乏么乏") ∷
   rw 41 q3 ∷
   re 42 5 (ℓ "中") ∷
   rw 44 q4 ∷
   rw⁻ 43 q5 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q6 ∷
   rw 43 q15 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q16 ∷
   rw 42 q5 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q6 ∷
   rw 44 q17 ∷
   rw 45 q6 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q10 ∷
   rw 41 q4 ∷
   rw⁻ 40 q5 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q6 ∷
   rw 40 q15 ∷
   rw⁻ 39 q6 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q16 ∷
   rw 39 q5 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q6 ∷
   rw 41 q17 ∷
   rw 42 q6 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q10 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q13 ∷
   re 44 3 (ℓ "乕") ∷
   rw 43 q14 ∷
   rw 42 q18 ∷
   rw 41 q2 ∷
   re 41 1 (ℓ "乏么乏") ∷
   rw 40 q3 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q4 ∷
   rw⁻ 42 q5 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q6 ∷
   rw 42 q15 ∷
   rw⁻ 41 q6 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q16 ∷
   rw 41 q5 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q6 ∷
   rw 43 q17 ∷
   rw 44 q6 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q10 ∷
   rw⁻ 38 q11 ∷
   rw⁻ 39 q12 ∷
   rw⁻ 40 q11 ∷
   rw 39 q4 ∷
   rw⁻ 38 q5 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q6 ∷
   rw 38 q7 ∷
   rw⁻ 37 q6 ∷
   re 38 3 (ℓ "乔") ∷
   rw 38 q8 ∷
   rw 37 q5 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q6 ∷
   rw 39 q9 ∷
   rw 40 q6 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q10 ∷
   re 38 1 (ℓ "乏丼临丼乏") ∷
   rw 44 q13 ∷
   re 42 3 (ℓ "乕") ∷
   rw 41 q14 ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 39 1 (ℓ "乏么乏") ∷
   rw 38 q3 ∷
   re 39 5 (ℓ "乑") ∷
   rw 41 q4 ∷
   rw⁻ 40 q5 ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw⁻ 41 q6 ∷
   rw 40 q7 ∷
   rw⁻ 39 q6 ∷
   re 40 3 (ℓ "乔") ∷
   rw 40 q8 ∷
   rw 39 q5 ∷
   re 41 1 (ℓ "乏乇乏") ∷
   rw 40 q6 ∷
   rw 41 q9 ∷
   rw 42 q6 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q10 ∷
   rw⁻ 36 q11 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 38 q11 ∷
   rw⁻ 35 q11 ∷
   rw⁻ 36 q12 ∷
   rw⁻ 37 q11 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q12 ∷
   rw⁻ 36 q11 ∷
   rw 35 q4 ∷
   rw⁻ 34 q5 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q6 ∷
   rw 34 q15 ∷
   rw⁻ 33 q6 ∷
   re 34 3 (ℓ "丽") ∷
   rw 34 q16 ∷
   rw 33 q5 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q6 ∷
   rw 35 q17 ∷
   rw 36 q6 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q10 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q13 ∷
   re 38 3 (ℓ "乕") ∷ []) Eq.refl
