{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D406 (W : Ws) where

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
  q2 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 464 W
  q6 : Eqn
  q6 = wE 1133 W
  q7 : Eqn
  q7 = wE 151 W
  q8 : Eqn
  q8 = wE 157 W
  q9 : Eqn
  q9 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q10 : Eqn
  q10 = wE 158 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 589 W
  q13 : Eqn
  q13 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q14 : Eqn
  q14 = wE 1115 W
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = wE 7 W
  q17 : Eqn
  q17 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q18 : Eqn
  q18 = wE 140 W
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 763 W
  q21 : Eqn
  q21 = wE 142 W
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 31 W
  q24 : Eqn
  q24 = wE 36 W
  q25 : Eqn
  q25 = wE 37 W
  q26 : Eqn
  q26 = wE 883 W
  q27 : Eqn
  q27 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] part0: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part0 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临丹丠丠临丠临临乀乑业乑业乏丧乏並丽丽乔业丽丽丽丽丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並乀中中乑中乑乑丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part0 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") (ℓ "丠丠临丠临临丹丠丠临丠临临乀乑业乑业乏丧乏並丽丽乔业丽丽丽丽丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並乀中中乑中乑乑丹丧丧乄丧乄乄")
  (rw 35 q1 ∷
   rw 34 q2 ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q3 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q4 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q4 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q4 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q4 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q4 ∷
   rw 15 q5 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q4 ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q4 ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q4 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q4 ∷
   rw 5 q2 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q6 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q2 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乀") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q7 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q7 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q7 ∷
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
   re 28 3 (ℓ "乀") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乑") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q4 ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q8 ∷
   rw 36 q9 ∷
   rw 35 q10 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q4 ∷
   re 35 5 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丼临丼乏") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q8 ∷
   rw 35 q9 ∷
   rw 34 q10 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q4 ∷
   re 34 5 (ℓ "乑") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q8 ∷
   rw 34 q11 ∷
   rw 33 q10 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q4 ∷
   re 33 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q8 ∷
   rw 33 q9 ∷
   rw 32 q10 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q4 ∷
   re 32 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q8 ∷
   rw 32 q11 ∷
   rw 31 q10 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q8 ∷
   rw 31 q11 ∷
   rw 30 q10 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "中") ∷
   rw 28 q12 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乀") ∷
   rw 30 q8 ∷
   rw 29 q11 ∷
   rw 28 q10 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q8 ∷
   rw 28 q11 ∷
   rw 27 q10 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q8 ∷
   rw 27 q11 ∷
   rw 26 q10 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q4 ∷
   re 26 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乀") ∷
   rw 27 q8 ∷
   rw 26 q11 ∷
   rw 25 q10 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 24 q4 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乀") ∷
   rw 26 q8 ∷
   rw 25 q11 ∷
   rw 24 q10 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q4 ∷
   re 24 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "乀") ∷
   rw 25 q8 ∷
   rw 24 q11 ∷
   rw 23 q10 ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 22 q4 ∷
   re 23 5 (ℓ "中") ∷
   rw⁻ 21 q13 ∷
   re 20 1 (ℓ "乏丼临丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乀") ∷
   rw 23 q8 ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 20 q4 ∷
   re 21 5 (ℓ "乑") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乀") ∷
   rw 22 q8 ∷
   rw 21 q11 ∷
   rw 20 q10 ∷
   re 20 1 (ℓ "乏丹乏") ∷
   rw 19 q4 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乀") ∷
   rw 21 q8 ∷
   rw 20 q11 ∷
   rw 19 q10 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 18 q4 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "乀") ∷
   rw 20 q8 ∷
   rw 19 q11 ∷
   rw 18 q10 ∷
   re 18 1 (ℓ "乏丹乏") ∷
   rw 17 q4 ∷
   re 18 5 (ℓ "中") ∷
   rw⁻ 16 q13 ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乀") ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   re 16 1 (ℓ "乏丹乏") ∷
   rw 15 q4 ∷
   re 16 5 (ℓ "乑") ∷
   rw⁻ 14 q13 ∷
   re 13 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乀") ∷
   rw 16 q8 ∷
   rw 15 q9 ∷
   rw 14 q10 ∷
   re 14 1 (ℓ "乏丹乏") ∷
   rw 13 q4 ∷
   re 14 5 (ℓ "乑") ∷
   rw 12 q12 ∷
   rw 6 q14 ∷
   rw 51 q15 ∷
   rw 50 q16 ∷
   rw 49 q16 ∷
   rw 48 q16 ∷
   rw 47 q16 ∷
   rw 46 q16 ∷
   rw 45 q16 ∷
   rw⁻ 44 q17 ∷
   rw 43 q18 ∷
   rw 42 q16 ∷
   rw 41 q16 ∷
   rw 40 q16 ∷
   rw⁻ 39 q17 ∷
   rw 38 q18 ∷
   rw⁻ 37 q17 ∷
   rw 36 q18 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q19 ∷
   rw 36 q18 ∷
   rw⁻ 35 q19 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q19 ∷
   rw 35 q18 ∷
   rw⁻ 34 q19 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q19 ∷
   rw 34 q16 ∷
   rw⁻ 33 q19 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q19 ∷
   rw 33 q18 ∷
   rw⁻ 32 q19 ∷
   re 33 3 (ℓ "乔") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q19 ∷
   rw 32 q16 ∷
   rw⁻ 31 q19 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q19 ∷
   rw 31 q16 ∷
   rw⁻ 30 q19 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q20 ∷
   rw 30 q21 ∷
   rw 31 q17 ∷
   rw 32 q21 ∷
   rw 33 q17 ∷
   rw 34 q22 ∷
   rw 35 q22 ∷
   rw 36 q22 ∷
   rw 37 q21 ∷
   rw 38 q17 ∷
   rw 39 q22 ∷
   rw 40 q22 ∷
   rw 41 q22 ∷
   rw 42 q22 ∷
   rw 43 q22 ∷
   rw 44 q22 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q19 ∷
   rw 46 q22 ∷
   rw 47 q19 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q19 ∷
   rw 47 q22 ∷
   rw 48 q19 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏乇乏") ∷
   rw 47 q19 ∷
   rw 48 q21 ∷
   rw 49 q19 ∷
   re 47 3 (ℓ "乑") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q19 ∷
   rw 49 q22 ∷
   rw 50 q19 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q19 ∷
   rw 50 q21 ∷
   rw 51 q19 ∷
   re 49 3 (ℓ "乑") ∷
   re 51 1 (ℓ "乏乇乏") ∷
   rw 50 q19 ∷
   rw 51 q21 ∷
   rw 52 q19 ∷
   re 50 3 (ℓ "乑") ∷
   rw 51 q23 ∷
   re 30 1 (ℓ "丼临丼") ∷
   rw 29 q24 ∷
   rw⁻ 30 q9 ∷
   rw 31 q25 ∷
   re 29 3 (ℓ "乄") ∷
   rw 30 q26 ∷
   re 32 1 (ℓ "丼临丼") ∷
   rw 31 q24 ∷
   rw⁻ 32 q9 ∷
   rw 33 q25 ∷
   re 31 3 (ℓ "乄") ∷
   rw 32 q26 ∷
   re 34 1 (ℓ "丼丠丼") ∷
   rw 33 q24 ∷
   rw⁻ 34 q11 ∷
   rw 35 q25 ∷
   re 33 3 (ℓ "丧") ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 34 q24 ∷
   rw⁻ 35 q11 ∷
   rw 36 q25 ∷
   re 34 3 (ℓ "丧") ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q24 ∷
   rw⁻ 36 q11 ∷
   rw 37 q25 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼临丼") ∷
   rw 36 q24 ∷
   rw⁻ 37 q9 ∷
   rw 38 q25 ∷
   re 36 3 (ℓ "乄") ∷
   rw 37 q26 ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q24 ∷
   rw⁻ 39 q11 ∷
   rw 40 q25 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q24 ∷
   rw⁻ 40 q11 ∷
   rw 41 q25 ∷
   re 39 3 (ℓ "丧") ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 40 q24 ∷
   rw⁻ 41 q11 ∷
   rw 42 q25 ∷
   re 40 3 (ℓ "丧") ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 41 q24 ∷
   rw⁻ 42 q11 ∷
   rw 43 q25 ∷
   re 41 3 (ℓ "丧") ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q24 ∷
   rw⁻ 43 q11 ∷
   rw 44 q25 ∷
   re 42 3 (ℓ "丧") ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q24 ∷
   rw⁻ 44 q11 ∷
   rw 45 q25 ∷
   re 43 3 (ℓ "丧") ∷
   rw 44 q15 ∷
   rw 43 q16 ∷
   rw 42 q16 ∷
   rw 41 q16 ∷
   rw 40 q16 ∷
   rw 39 q16 ∷
   rw 38 q16 ∷
   rw⁻ 37 q17 ∷
   rw 36 q18 ∷
   rw 35 q16 ∷
   rw 34 q16 ∷
   rw 33 q16 ∷
   rw⁻ 32 q17 ∷
   rw 31 q18 ∷
   rw⁻ 30 q17 ∷
   rw 29 q18 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q19 ∷
   rw 29 q16 ∷
   rw⁻ 28 q19 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q19 ∷
   rw 28 q16 ∷
   rw⁻ 27 q19 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q19 ∷
   rw 27 q16 ∷
   rw⁻ 26 q19 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q19 ∷
   rw 26 q16 ∷
   rw⁻ 25 q19 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q19 ∷
   rw 25 q16 ∷
   rw⁻ 24 q19 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q19 ∷
   rw 24 q16 ∷
   rw⁻ 23 q19 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q27 ∷
   re 21 1 (ℓ "乏乄乏") ∷
   rw⁻ 23 q19 ∷
   rw 22 q18 ∷
   rw⁻ 21 q19 ∷
   re 22 3 (ℓ "乔") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q19 ∷
   rw 21 q16 ∷
   rw⁻ 20 q19 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q19 ∷
   rw 20 q16 ∷
   rw⁻ 19 q19 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷ []) Eq.refl
