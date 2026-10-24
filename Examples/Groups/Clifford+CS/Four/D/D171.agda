{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D171 (W : Ws) where

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
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 630 W
  q6 : Eqn
  q6 = wE 142 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 21 W
  q10 : Eqn
  q10 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q11 : Eqn
  q11 = wE 51 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 360 W
  q14 : Eqn
  q14 = eqn (ℓ "临乘") (ℓ "乘临") (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q15 : Eqn
  q15 = wE 362 W
  q16 : Eqn
  q16 = wE 20 W
  q17 : Eqn
  q17 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q18 : Eqn
  q18 = wE 49 W
  q19 : Eqn
  q19 = wE 7 W
  q20 : Eqn
  q20 = wE 629 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q23 : Eqn
  q23 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q24 : Eqn
  q24 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q25 : Eqn
  q25 = wE 751 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CSd12 CKd21 CS12 CS12 X2] part0: 500 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part0 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丷么丶丶丘") ⟫ʷ ≈ ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘丷么乏丼丠义丼乏丶丘中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part0 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丷么丶丶丘") (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘丷么乏丼丠义丼乏丶丘中乌中中乑中乑乑")
  (rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "乔") ∷
   rw 29 q5 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   rw 30 q6 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q7 ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q12 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q8 ∷
   re 34 3 (ℓ "乕") ∷
   rw 33 q13 ∷
   rw 32 q14 ∷
   rw 31 q15 ∷
   re 31 1 (ℓ "乏么乏") ∷
   rw 30 q12 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "丽") ∷
   rw 34 q16 ∷
   rw 33 q17 ∷
   rw 32 q18 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q12 ∷
   re 32 5 (ℓ "乑") ∷
   re 32 1 (ℓ "乏丼临丼乏") ∷
   rw 38 q8 ∷
   re 36 3 (ℓ "丽") ∷
   rw 35 q16 ∷
   rw 34 q17 ∷
   rw 33 q18 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q12 ∷
   re 33 5 (ℓ "乑") ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q4 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "乔") ∷
   rw 34 q5 ∷
   rw 33 q2 ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q3 ∷
   rw 35 q6 ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q7 ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "乔") ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q7 ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q12 ∷
   re 29 5 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "乕") ∷
   rw 32 q13 ∷
   rw 31 q14 ∷
   rw 30 q15 ∷
   re 30 1 (ℓ "乏么乏") ∷
   rw 29 q12 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q8 ∷
   re 34 3 (ℓ "丽") ∷
   rw 33 q16 ∷
   rw 32 q17 ∷
   rw 31 q18 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q12 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "丽") ∷
   rw 34 q16 ∷
   rw 33 q17 ∷
   rw 32 q18 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q12 ∷
   re 32 5 (ℓ "乑") ∷
   rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乔") ∷
   rw 33 q5 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q3 ∷
   rw 34 q6 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q7 ∷
   rw 28 q1 ∷
   rw⁻ 27 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q19 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q20 ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   rw 28 q21 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q7 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q9 ∷
   rw 29 q22 ∷
   rw 28 q11 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q12 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "乕") ∷
   rw 31 q13 ∷
   rw 30 q23 ∷
   rw 29 q15 ∷
   re 29 1 (ℓ "乏么乏") ∷
   rw 28 q12 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q16 ∷
   rw 31 q24 ∷
   rw 30 q18 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q12 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q8 ∷
   re 34 3 (ℓ "丽") ∷
   rw 33 q16 ∷
   rw 32 q24 ∷
   rw 31 q18 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q12 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q19 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q20 ∷
   rw 31 q2 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q3 ∷
   rw 33 q21 ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q7 ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "乔") ∷
   rw 26 q5 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q3 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "乑") ∷
   rw 27 q7 ∷
   re 26 1 (ℓ "乏丼临丼乏") ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q12 ∷
   re 27 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "乕") ∷
   rw 30 q13 ∷
   rw 29 q14 ∷
   rw 28 q15 ∷
   re 28 1 (ℓ "乏么乏") ∷
   rw 27 q12 ∷
   re 28 5 (ℓ "乑") ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q12 ∷
   re 29 5 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q16 ∷
   rw 31 q17 ∷
   rw 30 q18 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q12 ∷
   re 30 5 (ℓ "乑") ∷
   rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q5 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q3 ∷
   rw 32 q6 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q7 ∷
   rw 26 q1 ∷
   rw⁻ 25 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q19 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q20 ∷
   rw 24 q2 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   rw 26 q21 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q7 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q8 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q9 ∷
   rw 27 q22 ∷
   rw 26 q11 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q12 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "乕") ∷
   rw 29 q13 ∷
   rw 28 q23 ∷
   rw 27 q15 ∷
   re 27 1 (ℓ "乏么乏") ∷
   rw 26 q12 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q16 ∷
   rw 29 q24 ∷
   rw 28 q18 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q12 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q16 ∷
   rw 30 q24 ∷
   rw 29 q18 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q12 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q19 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q20 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q21 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q7 ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q19 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q20 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q21 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q8 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q9 ∷
   rw 26 q22 ∷
   rw 25 q11 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q12 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q8 ∷
   re 29 3 (ℓ "乕") ∷
   rw 28 q13 ∷
   rw 27 q23 ∷
   rw 26 q15 ∷
   re 26 1 (ℓ "乏么乏") ∷
   rw 25 q12 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q16 ∷
   rw 28 q24 ∷
   rw 27 q18 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q12 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q16 ∷
   rw 29 q24 ∷
   rw 28 q18 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q12 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q19 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q20 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q3 ∷
   rw 30 q21 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q7 ∷
   rw 22 q25 ∷
   rw 23 q1 ∷
   rw⁻ 22 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q19 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q20 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q21 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q7 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q8 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q9 ∷
   rw 24 q22 ∷
   rw 23 q11 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q12 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q8 ∷
   re 27 3 (ℓ "乕") ∷
   rw 26 q13 ∷
   rw 25 q23 ∷
   rw 24 q15 ∷
   re 24 1 (ℓ "乏么乏") ∷
   rw 23 q12 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q8 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q16 ∷
   rw 26 q24 ∷
   rw 25 q18 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q12 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q8 ∷
   re 29 3 (ℓ "丽") ∷
   rw 28 q16 ∷
   rw 27 q24 ∷
   rw 26 q18 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q12 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q1 ∷
   rw⁻ 27 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q19 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q20 ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   rw 28 q21 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q7 ∷
   rw 22 q1 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q19 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q20 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q21 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q7 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q8 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q9 ∷
   rw 23 q22 ∷
   rw 22 q11 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q12 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q8 ∷
   re 26 3 (ℓ "乕") ∷
   rw 25 q13 ∷
   rw 24 q23 ∷
   rw 23 q15 ∷
   re 23 1 (ℓ "乏么乏") ∷
   rw 22 q12 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q8 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q16 ∷ []) Eq.refl
