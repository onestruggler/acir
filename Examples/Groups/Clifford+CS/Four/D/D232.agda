{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D232 (W : Ws) where

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
  q9 = wE 360 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q11 : Eqn
  q11 = wE 362 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = wE 630 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = eqn (ℓ "临乘") (ℓ "乘临") (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q17 : Eqn
  q17 = wE 645 W
  q18 : Eqn
  q18 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q19 : Eqn
  q19 = eqn (ℓ "么业") (ℓ "业么") (low₃-comm (((S ↑ • CK₁₀) ↑)) (S))
  q20 : Eqn
  q20 = wE 503 W
  q21 : Eqn
  q21 = wE 502 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CKd21 X2]: 869 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘么丘") ⟫ʷ ≈ ⟪ (ℓ "丘么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd21-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘么丘") (ℓ "丘么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q5 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   rw 32 q6 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q7 ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "乕") ∷
   rw 34 q9 ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   re 32 1 (ℓ "乏么乏") ∷
   rw 31 q12 ∷
   re 32 5 (ℓ "中") ∷
   rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q5 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q3 ∷
   rw 34 q6 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q7 ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q6 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q7 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q8 ∷
   re 34 3 (ℓ "乕") ∷
   rw 33 q9 ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   re 31 1 (ℓ "乏么乏") ∷
   rw 30 q12 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q4 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q5 ∷
   rw 31 q2 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q3 ∷
   rw 33 q6 ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q7 ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q13 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "乔") ∷
   rw 29 q14 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   rw 30 q15 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q7 ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "乕") ∷
   rw 32 q9 ∷
   rw 31 q16 ∷
   rw 30 q11 ∷
   re 30 1 (ℓ "乏么乏") ∷
   rw 29 q12 ∷
   re 30 5 (ℓ "乑") ∷
   rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q13 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q14 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q3 ∷
   rw 32 q15 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q7 ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q7 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "乕") ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   re 29 1 (ℓ "乏么乏") ∷
   rw 28 q12 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q6 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q7 ∷
   rw 28 q1 ∷
   rw⁻ 27 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q4 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q5 ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   rw 28 q6 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q7 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "乕") ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   re 28 1 (ℓ "乏么乏") ∷
   rw 27 q12 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q5 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q3 ∷
   rw 30 q6 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q7 ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q5 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q7 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "乕") ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   re 27 1 (ℓ "乏么乏") ∷
   rw 26 q12 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q7 ∷
   rw 24 q17 ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q4 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q5 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q6 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q8 ∷
   re 28 3 (ℓ "乕") ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   re 25 1 (ℓ "乏么乏") ∷
   rw 24 q12 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q5 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q7 ∷
   rw 24 q1 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q4 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q5 ∷
   rw 22 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   rw 24 q6 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q7 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q8 ∷
   re 27 3 (ℓ "乕") ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q11 ∷
   re 24 1 (ℓ "乏么乏") ∷
   rw 23 q12 ∷
   re 24 5 (ℓ "中") ∷
   rw 26 q1 ∷
   rw⁻ 25 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q4 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q5 ∷
   rw 24 q2 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   rw 26 q6 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q7 ∷
   rw 23 q1 ∷
   rw⁻ 22 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q5 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q6 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q7 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q8 ∷
   re 26 3 (ℓ "乕") ∷
   rw 25 q9 ∷
   rw 24 q10 ∷
   rw 23 q11 ∷
   re 23 1 (ℓ "乏么乏") ∷
   rw 22 q12 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q4 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q5 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q6 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q7 ∷
   rw 22 q1 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q4 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q5 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q6 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q7 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q8 ∷
   re 25 3 (ℓ "乕") ∷
   rw 24 q9 ∷
   rw 23 q10 ∷
   rw 22 q11 ∷
   re 22 1 (ℓ "乏么乏") ∷
   rw 21 q12 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q1 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q4 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q5 ∷
   rw 22 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   rw 24 q6 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q7 ∷
   rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q4 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q5 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q6 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q7 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q8 ∷
   re 24 3 (ℓ "乕") ∷
   rw 23 q9 ∷
   rw 22 q10 ∷
   rw 21 q11 ∷
   re 21 1 (ℓ "乏么乏") ∷
   rw 20 q12 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q1 ∷
   rw⁻ 22 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q5 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q6 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q7 ∷
   rw 20 q1 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q4 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q5 ∷
   rw 18 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   rw 20 q6 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q7 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q8 ∷
   re 23 3 (ℓ "乕") ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   rw 20 q11 ∷
   re 20 1 (ℓ "乏么乏") ∷
   rw 19 q12 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q1 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q4 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q5 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q6 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q7 ∷
   rw 19 q1 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q4 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q5 ∷
   rw 17 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 19 q6 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q7 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q8 ∷
   re 22 3 (ℓ "乕") ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   rw 19 q11 ∷
   re 19 1 (ℓ "乏么乏") ∷
   rw 18 q12 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q4 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q5 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q6 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q7 ∷
   rw 18 q1 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q4 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q5 ∷
   rw 16 q2 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   rw 18 q6 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q7 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q8 ∷
   re 21 3 (ℓ "乕") ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q11 ∷
   re 18 1 (ℓ "乏么乏") ∷
   rw 17 q12 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q1 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q4 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q5 ∷
   rw 18 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   rw 20 q6 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q7 ∷
   rw 17 q1 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q4 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q5 ∷
   rw 15 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw 17 q6 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q7 ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q8 ∷
   re 20 3 (ℓ "乕") ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   rw 17 q11 ∷
   re 17 1 (ℓ "乏么乏") ∷
   rw 16 q12 ∷
   re 17 5 (ℓ "中") ∷
   rw 19 q1 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q4 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q5 ∷
   rw 17 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 19 q6 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q7 ∷
   rw⁻ 14 q18 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q18 ∷
   rw 15 q1 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q13 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "乔") ∷
   rw 14 q14 ∷
   rw 13 q2 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q3 ∷
   rw 15 q15 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q7 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q8 ∷
   re 18 3 (ℓ "乕") ∷
   rw 17 q9 ∷
   rw 16 q16 ∷
   rw 15 q11 ∷
   re 15 1 (ℓ "乏么乏") ∷
   rw 14 q12 ∷
   re 15 5 (ℓ "乑") ∷
   rw 17 q1 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q13 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "乔") ∷
   rw 16 q14 ∷
   rw 15 q2 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q3 ∷
   rw 17 q15 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q7 ∷
   rw 14 q1 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q4 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q5 ∷
   rw 12 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 14 q6 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q7 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q8 ∷
   re 17 3 (ℓ "乕") ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   re 14 1 (ℓ "乏么乏") ∷
   rw 13 q12 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q1 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q4 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q5 ∷
   rw 14 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   rw 16 q6 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q7 ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q4 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q5 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   rw 13 q6 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q7 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q8 ∷
   re 16 3 (ℓ "乕") ∷
   rw 15 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   re 13 1 (ℓ "乏么乏") ∷
   rw 12 q12 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q1 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q4 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q5 ∷
   rw 13 q2 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   rw 15 q6 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q7 ∷
   rw 12 q1 ∷
   rw⁻ 11 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q3 ∷
   rw 11 q4 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 12 q6 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q7 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q8 ∷
   re 15 3 (ℓ "乕") ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   re 12 1 (ℓ "乏么乏") ∷
   rw 11 q12 ∷
   re 12 5 (ℓ "中") ∷
   rw 14 q1 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q4 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q5 ∷
   rw 12 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 14 q6 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q7 ∷
   rw 11 q1 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q4 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q3 ∷
   rw 11 q6 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q7 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q8 ∷
   re 14 3 (ℓ "乕") ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   rw 11 q11 ∷
   re 11 1 (ℓ "乏么乏") ∷
   rw 10 q12 ∷
   re 11 5 (ℓ "中") ∷
   rw 13 q1 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q4 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q5 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   rw 13 q6 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q7 ∷
   rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q3 ∷
   rw 9 q4 ∷
   rw⁻ 8 q3 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q5 ∷
   rw 8 q2 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q3 ∷
   rw 10 q6 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q7 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q8 ∷
   re 13 3 (ℓ "乕") ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   re 10 1 (ℓ "乏么乏") ∷
   rw 9 q12 ∷
   re 10 5 (ℓ "中") ∷
   rw 12 q1 ∷
   rw⁻ 11 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q3 ∷
   rw 11 q4 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 12 q6 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q7 ∷
   rw 9 q1 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q3 ∷
   rw 8 q4 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (ℓ "丽") ∷
   rw 8 q5 ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q6 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q7 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "乕") ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 9 1 (ℓ "乏么乏") ∷
   rw 8 q12 ∷
   re 9 5 (ℓ "中") ∷
   rw 11 q1 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q4 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q3 ∷
   rw 11 q6 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q7 ∷
   rw 6 q17 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q20 ∷
   rw 0 q20 ∷ []) Eq.refl
