{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D213 (W : Ws) where

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
  q1 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q2 : Eqn
  q2 = wE 49 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 360 W
  q6 : Eqn
  q6 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q7 : Eqn
  q7 = wE 362 W
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 629 W
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 359 W
  q16 : Eqn
  q16 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q17 : Eqn
  q17 = wE 361 W
  q18 : Eqn
  q18 = wE 20 W
  q19 : Eqn
  q19 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q20 : Eqn
  q20 = eqn (ℓ "乇业") (ℓ "业乇") (low₃-comm ((CK₁₀ ↑)) (S))
  q21 : Eqn
  q21 = eqn (ℓ "丶业") (ℓ "业丶") (low₃-comm ((CS ↑)) (S))
  q22 : Eqn
  q22 = eqn (ℓ "么业") (ℓ "业么") (low₃-comm (((S ↑ • CK₁₀) ↑)) (S))
  q23 : Eqn
  q23 = wE 140 W
  q24 : Eqn
  q24 = wE 630 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q27 : Eqn
  q27 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q28 : Eqn
  q28 = eqn (ℓ "临乘") (ℓ "乘临") (low-comm (CK₁₀) ((S ↑ • CK₁₀)))

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK21 CS12 CS12 CKd21 X2] part1: 500 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-CS12-CS12-CKd21-X2-part1 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘乇丶乏丼丠义丼乏么丘中乌中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业乏丧乏並丘並乇丶丶么丘中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK21-CS12-CS12-CKd21-X2-part1 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘乇丶乏丼丠义丼乏么丘中乌中中乑中乑乑") (ℓ "丧丧乄丧乄乄乌乑业乑业乏丧乏並丘並乇丶丶么丘中中乑业中中中中中中乌中中乑中乑乑")
  (rw 25 q1 ∷
   rw 24 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "乕") ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   re 25 1 (ℓ "乏么乏") ∷
   rw 24 q3 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q10 ∷
   rw 26 q11 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q12 ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q10 ∷
   rw 27 q13 ∷
   rw 28 q10 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q14 ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q10 ∷
   rw 20 q11 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q12 ∷
   rw 19 q9 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q10 ∷
   rw 21 q13 ∷
   rw 22 q10 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q14 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "乔") ∷
   rw 23 q15 ∷
   rw 22 q16 ∷
   rw 21 q17 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q3 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q18 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q18 ∷
   rw 24 q1 ∷
   rw 23 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "乕") ∷
   rw 26 q5 ∷
   rw 25 q6 ∷
   rw 24 q7 ∷
   re 24 1 (ℓ "乏么乏") ∷
   rw 23 q3 ∷
   re 24 5 (ℓ "中") ∷
   rw 26 q8 ∷
   rw⁻ 25 q9 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q10 ∷
   rw 25 q11 ∷
   rw⁻ 24 q10 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q12 ∷
   rw 24 q9 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q10 ∷
   rw 26 q13 ∷
   rw 27 q10 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q14 ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q10 ∷
   rw 19 q11 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q12 ∷
   rw 18 q9 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q10 ∷
   rw 20 q13 ∷
   rw 21 q10 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q14 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "乔") ∷
   rw 22 q15 ∷
   rw 21 q16 ∷
   rw 20 q17 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q3 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q18 ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q18 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "乕") ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q7 ∷
   re 23 1 (ℓ "乏么乏") ∷
   rw 22 q3 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q10 ∷
   rw 24 q11 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q12 ∷
   rw 23 q9 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q10 ∷
   rw 25 q13 ∷
   rw 26 q10 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q14 ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q10 ∷
   rw 18 q11 ∷
   rw⁻ 17 q10 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q12 ∷
   rw 17 q9 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q10 ∷
   rw 19 q13 ∷
   rw 20 q10 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q14 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "乔") ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   rw 19 q17 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q3 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q18 ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q18 ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "乕") ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   re 22 1 (ℓ "乏么乏") ∷
   rw 21 q3 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q8 ∷
   rw⁻ 23 q9 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q10 ∷
   rw 23 q11 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q12 ∷
   rw 22 q9 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q10 ∷
   rw 24 q13 ∷
   rw 25 q10 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q14 ∷
   rw 18 q8 ∷
   rw⁻ 17 q9 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q10 ∷
   rw 17 q11 ∷
   rw⁻ 16 q10 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q12 ∷
   rw 16 q9 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q10 ∷
   rw 18 q13 ∷
   rw 19 q10 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q14 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "乔") ∷
   rw 20 q15 ∷
   rw 19 q16 ∷
   rw 18 q17 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q3 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q18 ∷
   rw 20 q1 ∷
   rw 19 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q18 ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "乕") ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   re 21 1 (ℓ "乏么乏") ∷
   rw 20 q3 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q10 ∷
   rw 22 q11 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q12 ∷
   rw 21 q9 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q10 ∷
   rw 23 q13 ∷
   rw 24 q10 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q14 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q20 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q22 ∷
   rw⁻ 20 q19 ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q10 ∷
   rw 15 q23 ∷
   rw⁻ 14 q10 ∷
   re 15 3 (ℓ "乔") ∷
   rw 15 q24 ∷
   rw 14 q9 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q10 ∷
   rw 16 q25 ∷
   rw 17 q10 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q14 ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "乔") ∷
   rw 18 q15 ∷
   rw 17 q26 ∷
   rw 16 q17 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q3 ∷
   re 16 5 (ℓ "乑") ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q18 ∷
   rw 18 q27 ∷
   rw 17 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   re 17 5 (ℓ "乑") ∷
   re 17 1 (ℓ "乏丼临丼乏") ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q18 ∷
   rw 19 q27 ∷
   rw 18 q2 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   re 18 5 (ℓ "乑") ∷
   re 18 1 (ℓ "乏丼临丼乏") ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "乕") ∷
   rw 21 q5 ∷
   rw 20 q28 ∷
   rw 19 q7 ∷
   re 19 1 (ℓ "乏么乏") ∷
   rw 18 q3 ∷
   re 19 5 (ℓ "乑") ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw⁻ 21 q10 ∷
   rw 20 q23 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (ℓ "乔") ∷
   rw 20 q24 ∷
   rw 19 q9 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q10 ∷
   rw 21 q25 ∷
   rw 22 q10 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q14 ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q10 ∷
   rw 14 q11 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q12 ∷
   rw 13 q9 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q10 ∷
   rw 15 q13 ∷
   rw 16 q10 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q14 ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q4 ∷
   re 18 3 (ℓ "乔") ∷
   rw 17 q15 ∷
   rw 16 q16 ∷
   rw 15 q17 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q3 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "丽") ∷
   rw 18 q18 ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q18 ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "乕") ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q7 ∷
   re 18 1 (ℓ "乏么乏") ∷
   rw 17 q3 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q10 ∷
   rw 19 q11 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q12 ∷
   rw 18 q9 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q10 ∷
   rw 20 q13 ∷
   rw 21 q10 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q14 ∷
   rw 14 q8 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q10 ∷
   rw 13 q11 ∷
   rw⁻ 12 q10 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q12 ∷
   rw 12 q9 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q10 ∷
   rw 14 q13 ∷
   rw 15 q10 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q14 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q4 ∷
   re 17 3 (ℓ "乔") ∷
   rw 16 q15 ∷
   rw 15 q16 ∷
   rw 14 q17 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q3 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q4 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q18 ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "丽") ∷
   rw 18 q18 ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "乕") ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   rw 17 q7 ∷
   re 17 1 (ℓ "乏么乏") ∷
   rw 16 q3 ∷
   re 17 5 (ℓ "中") ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q10 ∷
   rw 18 q11 ∷
   rw⁻ 17 q10 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q12 ∷
   rw 17 q9 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q10 ∷
   rw 19 q13 ∷
   rw 20 q10 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q14 ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (ℓ "乏丧乏") ∷ []) Eq.refl
