{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D395 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q6 : Eqn
  q6 = wE 140 W
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 1120 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 36 W
  q14 : Eqn
  q14 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q15 : Eqn
  q15 = wE 37 W
  q16 : Eqn
  q16 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q17 : Eqn
  q17 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q18 : Eqn
  q18 = wE 464 W
  q19 : Eqn
  q19 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = wE 1121 W
  q22 : Eqn
  q22 = wE 151 W
  q23 : Eqn
  q23 = wE 157 W
  q24 : Eqn
  q24 = wE 158 W
  q25 : Eqn
  q25 = wE 624 W
  q26 : Eqn
  q26 = wE 625 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03] part1: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part1 : ⟪ (ℓ "丠丠临丠乀丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中乑业中中中中中乏丼丠丼乀乏丧丧乄丧乄乄乀中中乑中") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠乀中中中乑业中中中中中中丠丠临丠临临丹乄且乄且丧乏乏丧乏丹乏丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄中中乑中") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part1 = derive (ℓ "丠丠临丠乀丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中乑业中中中中中乏丼丠丼乀乏丧丧乄丧乄乄乀中中乑中") (ℓ "丠丠临丠乀中中中乑业中中中中中中丠丠临丠临临丹乄且乄且丧乏乏丧乏丹乏丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄中中乑中")
  (re 41 1 (ℓ "乏丹乏") ∷
   rw 43 q1 ∷
   re 37 5 (ℓ "中") ∷
   rw 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q3 ∷
   rw 38 q4 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q3 ∷
   rw 37 q4 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q4 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q4 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   rw⁻ 31 q5 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q6 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "乔") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw⁻ 20 q7 ∷
   rw 19 q6 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw⁻ 15 q7 ∷
   rw 14 q6 ∷
   rw⁻ 13 q7 ∷
   rw 12 q6 ∷
   rw 13 q8 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   rw 15 q9 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q3 ∷
   rw 16 q10 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q5 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   rw 18 q9 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 19 q9 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   rw 20 q9 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q9 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q9 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q9 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q10 ∷
   rw 24 q7 ∷
   rw 25 q10 ∷
   rw 26 q7 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q10 ∷
   rw 31 q7 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q9 ∷
   rw 35 q9 ∷
   rw 36 q9 ∷
   rw 37 q9 ∷
   rw 38 q11 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q12 ∷
   re 12 3 (ℓ "乀") ∷
   rw 12 q13 ∷
   rw⁻ 13 q14 ∷
   rw 14 q15 ∷
   re 15 1 (ℓ "乏丹乏") ∷
   rw 17 q1 ∷
   re 11 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q12 ∷
   re 13 3 (ℓ "乀") ∷
   rw 13 q13 ∷
   rw⁻ 14 q14 ∷
   rw 15 q15 ∷
   re 16 1 (ℓ "乏丹乏") ∷
   rw 18 q1 ∷
   re 12 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q12 ∷
   re 14 3 (ℓ "乀") ∷
   rw 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw 16 q15 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 19 q1 ∷
   re 13 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q12 ∷
   re 15 3 (ℓ "乀") ∷
   rw 15 q13 ∷
   rw⁻ 16 q16 ∷
   rw 17 q15 ∷
   re 18 1 (ℓ "乏丹乏") ∷
   rw 20 q1 ∷
   re 14 5 (ℓ "乑") ∷
   rw 15 q17 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q12 ∷
   re 17 3 (ℓ "乀") ∷
   rw 17 q13 ∷
   rw⁻ 18 q14 ∷
   rw 19 q15 ∷
   re 20 1 (ℓ "乏丹乏") ∷
   rw 22 q1 ∷
   re 16 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q12 ∷
   re 18 3 (ℓ "乀") ∷
   rw 18 q13 ∷
   rw⁻ 19 q14 ∷
   rw 20 q15 ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 23 q1 ∷
   re 17 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q12 ∷
   re 19 3 (ℓ "乀") ∷
   rw 19 q13 ∷
   rw⁻ 20 q14 ∷
   rw 21 q15 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q1 ∷
   re 18 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q12 ∷
   re 20 3 (ℓ "乀") ∷
   rw 20 q13 ∷
   rw⁻ 21 q14 ∷
   rw 22 q15 ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 25 q1 ∷
   re 19 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q12 ∷
   re 21 3 (ℓ "乀") ∷
   rw 21 q13 ∷
   rw⁻ 22 q14 ∷
   rw 23 q15 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q1 ∷
   re 20 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q12 ∷
   re 22 3 (ℓ "乀") ∷
   rw 22 q13 ∷
   rw⁻ 23 q14 ∷
   rw 24 q15 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 27 q1 ∷
   re 21 5 (ℓ "中") ∷
   rw 22 q12 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q1 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q1 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q1 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q1 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q1 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q1 ∷
   rw 15 q18 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q1 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q1 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q1 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q1 ∷
   rw 10 q19 ∷
   rw 9 q19 ∷
   rw 8 q20 ∷
   rw 7 q19 ∷
   rw 6 q20 ∷
   rw 5 q20 ∷
   rw 6 q21 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q22 ∷
   rw 12 q12 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q12 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q12 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q12 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q12 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q12 ∷
   re 15 3 (ℓ "中") ∷
   rw⁻ 16 q20 ∷
   rw⁻ 17 q20 ∷
   rw⁻ 18 q19 ∷
   rw⁻ 19 q20 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw 22 q1 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q12 ∷
   re 45 3 (ℓ "乑") ∷
   re 45 1 (ℓ "乏丼临丼乏") ∷
   rw 51 q12 ∷
   re 49 3 (ℓ "乀") ∷
   rw 48 q23 ∷
   rw 47 q16 ∷
   rw 46 q24 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q1 ∷
   re 46 5 (ℓ "乑") ∷
   re 46 1 (ℓ "乏乄乏") ∷
   rw 48 q1 ∷
   re 44 3 (ℓ "乀") ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q12 ∷
   re 44 3 (ℓ "乑") ∷
   re 44 1 (ℓ "乏丼临丼乏") ∷
   rw 50 q12 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q23 ∷
   rw 46 q16 ∷
   rw 45 q24 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q1 ∷
   re 45 5 (ℓ "乑") ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw 47 q1 ∷
   re 43 3 (ℓ "乀") ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q12 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q12 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q23 ∷
   rw 45 q14 ∷
   rw 44 q24 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q1 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q1 ∷
   re 42 3 (ℓ "乀") ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q12 ∷
   re 42 3 (ℓ "乑") ∷
   re 42 1 (ℓ "乏丼临丼乏") ∷
   rw 48 q12 ∷
   re 46 3 (ℓ "乀") ∷
   rw 45 q23 ∷
   rw 44 q16 ∷
   rw 43 q24 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q1 ∷
   re 43 5 (ℓ "乑") ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw 45 q1 ∷
   re 41 3 (ℓ "乀") ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q12 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q12 ∷
   re 45 3 (ℓ "乀") ∷
   rw 44 q23 ∷
   rw 43 q14 ∷
   rw 42 q24 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q1 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q1 ∷
   re 40 3 (ℓ "乀") ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q12 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q12 ∷
   re 44 3 (ℓ "乀") ∷
   rw 43 q23 ∷
   rw 42 q14 ∷
   rw 41 q24 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q1 ∷
   re 39 3 (ℓ "乀") ∷
   rw 38 q25 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q12 ∷
   re 38 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q12 ∷
   re 42 3 (ℓ "乀") ∷
   rw 41 q23 ∷
   rw 40 q14 ∷
   rw 39 q24 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q1 ∷
   re 39 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q1 ∷
   re 37 3 (ℓ "乀") ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q12 ∷
   re 37 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q12 ∷
   re 41 3 (ℓ "乀") ∷
   rw 40 q23 ∷
   rw 39 q14 ∷
   rw 38 q24 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q1 ∷
   re 38 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q1 ∷
   re 36 3 (ℓ "乀") ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q12 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q12 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q23 ∷
   rw 38 q14 ∷
   rw 37 q24 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q1 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q1 ∷
   re 35 3 (ℓ "乀") ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q12 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q12 ∷
   re 39 3 (ℓ "乀") ∷
   rw 38 q23 ∷
   rw 37 q14 ∷
   rw 36 q24 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q1 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q1 ∷
   re 34 3 (ℓ "乀") ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q12 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q12 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q23 ∷
   rw 36 q14 ∷
   rw 35 q24 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q1 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q1 ∷
   re 33 3 (ℓ "乀") ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q12 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q12 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q23 ∷
   rw 35 q14 ∷
   rw 34 q24 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q1 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q1 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q26 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q12 ∷
   re 31 3 (ℓ "乑") ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 37 q12 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q23 ∷
   rw 33 q16 ∷
   rw 32 q24 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q1 ∷
   re 32 5 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw 34 q1 ∷
   re 30 3 (ℓ "乀") ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q12 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q12 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q23 ∷
   rw 32 q14 ∷
   rw 31 q24 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q1 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q1 ∷
   re 29 3 (ℓ "乀") ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q12 ∷ []) Eq.refl
