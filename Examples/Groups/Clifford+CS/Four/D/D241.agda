{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D241 (W : Ws) where

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
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 140 W
  q3 : Eqn
  q3 = wE 630 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 142 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 20 W
  q9 : Eqn
  q9 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q10 : Eqn
  q10 = wE 49 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 359 W
  q13 : Eqn
  q13 = eqn (ℓ "临乗") (ℓ "乗临") (low-comm (CK₁₀) (CK₁₀))
  q14 : Eqn
  q14 = wE 361 W
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = wE 629 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q20 : Eqn
  q20 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q21 : Eqn
  q21 = wE 746 W
  q22 : Eqn
  q22 = wE 748 W
  q23 : Eqn
  q23 = wE 747 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CS12 CS12 CK21 CS12 X2] part2: 466 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-CS12-CK21-CS12-X2-part2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乏乄乏並丘並丶丶乇丶丘业中中中中中中中中中乌中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丘丶丶乇丶丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS12-CS12-CK21-CS12-X2-part2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乏乄乏並丘並丶丶乇丶丘业中中中中中中中中中乌中中中乑中中") (ℓ "丘丶丶乇丶丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw⁻ 15 q1 ∷
   rw 14 q2 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (ℓ "乔") ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q1 ∷
   rw 15 q5 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q6 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q7 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q11 ∷
   re 15 5 (ℓ "乑") ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "丽") ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q11 ∷
   re 16 5 (ℓ "乑") ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q7 ∷
   re 20 3 (ℓ "乔") ∷
   rw 19 q12 ∷
   rw 18 q13 ∷
   rw 17 q14 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q11 ∷
   re 17 5 (ℓ "乑") ∷
   re 17 1 (ℓ "乏丼临丼乏") ∷
   rw 23 q7 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q11 ∷
   re 18 5 (ℓ "乑") ∷
   rw 20 q15 ∷
   rw⁻ 19 q4 ∷
   re 18 1 (ℓ "乏乄乏") ∷
   rw⁻ 20 q1 ∷
   rw 19 q2 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (ℓ "乔") ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q1 ∷
   rw 20 q5 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乑") ∷
   rw 20 q6 ∷
   rw 14 q15 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q16 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q17 ∷
   rw 12 q4 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q1 ∷
   rw 14 q18 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q6 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q8 ∷
   rw 15 q19 ∷
   rw 14 q10 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q7 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q8 ∷
   rw 16 q19 ∷
   rw 15 q10 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q11 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "乔") ∷
   rw 18 q12 ∷
   rw 17 q20 ∷
   rw 16 q14 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q11 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q7 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q8 ∷
   rw 18 q19 ∷
   rw 17 q10 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q11 ∷
   re 17 5 (ℓ "中") ∷
   rw 19 q15 ∷
   rw⁻ 18 q4 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q1 ∷
   rw 18 q16 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q17 ∷
   rw 17 q4 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q1 ∷
   rw 19 q18 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q6 ∷
   rw 13 q15 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q1 ∷
   rw 12 q16 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q17 ∷
   rw 11 q4 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q1 ∷
   rw 13 q18 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q6 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q8 ∷
   rw 14 q19 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q8 ∷
   rw 15 q19 ∷
   rw 14 q10 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q7 ∷
   re 18 3 (ℓ "乔") ∷
   rw 17 q12 ∷
   rw 16 q20 ∷
   rw 15 q14 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q11 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "丽") ∷
   rw 18 q8 ∷
   rw 17 q19 ∷
   rw 16 q10 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q11 ∷
   re 16 5 (ℓ "中") ∷
   rw 18 q15 ∷
   rw⁻ 17 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q1 ∷
   rw 17 q16 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q17 ∷
   rw 16 q4 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q1 ∷
   rw 18 q18 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q6 ∷
   rw 12 q15 ∷
   rw⁻ 11 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q1 ∷
   rw 11 q16 ∷
   rw⁻ 10 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q17 ∷
   rw 10 q4 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q1 ∷
   rw 12 q18 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q6 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q8 ∷
   rw 13 q19 ∷
   rw 12 q10 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q8 ∷
   rw 14 q19 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "乔") ∷
   rw 16 q12 ∷
   rw 15 q20 ∷
   rw 14 q14 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q7 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q8 ∷
   rw 16 q19 ∷
   rw 15 q10 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q11 ∷
   re 15 5 (ℓ "中") ∷
   rw 17 q15 ∷
   rw⁻ 16 q4 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q1 ∷
   rw 16 q16 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q17 ∷
   rw 15 q4 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q1 ∷
   rw 17 q18 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q6 ∷
   rw 11 q15 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q1 ∷
   rw 10 q16 ∷
   rw⁻ 9 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q17 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q1 ∷
   rw 11 q18 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q8 ∷
   rw 12 q19 ∷
   rw 11 q10 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q11 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q8 ∷
   rw 13 q19 ∷
   rw 12 q10 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "乔") ∷
   rw 15 q12 ∷
   rw 14 q20 ∷
   rw 13 q14 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q8 ∷
   rw 15 q19 ∷
   rw 14 q10 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q15 ∷
   rw⁻ 15 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q1 ∷
   rw 15 q16 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q17 ∷
   rw 14 q4 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q1 ∷
   rw 16 q18 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q6 ∷
   rw 10 q15 ∷
   rw⁻ 9 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q1 ∷
   rw 9 q16 ∷
   rw⁻ 8 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q17 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q1 ∷
   rw 10 q18 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q8 ∷
   rw 11 q19 ∷
   rw 10 q10 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q11 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q8 ∷
   rw 12 q19 ∷
   rw 11 q10 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q11 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "乔") ∷
   rw 14 q12 ∷
   rw 13 q20 ∷
   rw 12 q14 ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q8 ∷
   rw 14 q19 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q15 ∷
   rw⁻ 14 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q1 ∷
   rw 14 q16 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q17 ∷
   rw 13 q4 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q1 ∷
   rw 15 q18 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q6 ∷
   rw 9 q15 ∷
   rw⁻ 8 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q1 ∷
   rw 8 q16 ∷
   rw⁻ 7 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw 8 q17 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q1 ∷
   rw 9 q18 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "丽") ∷
   rw 11 q8 ∷
   rw 10 q19 ∷
   rw 9 q10 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q11 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q8 ∷
   rw 11 q19 ∷
   rw 10 q10 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q11 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "乔") ∷
   rw 13 q12 ∷
   rw 12 q20 ∷
   rw 11 q14 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q11 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q8 ∷
   rw 13 q19 ∷
   rw 12 q10 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "中") ∷
   rw 14 q15 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q16 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q17 ∷
   rw 12 q4 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q1 ∷
   rw 14 q18 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q6 ∷
   rw 6 q21 ∷
   rw 5 q22 ∷
   rw 4 q22 ∷
   rw 3 q23 ∷
   rw 2 q22 ∷
   rw 1 q22 ∷
   rw 0 q22 ∷ []) Eq.refl
