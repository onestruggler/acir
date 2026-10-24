{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D392 (W : Ws) where

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
  q2 = wE 151 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 157 W
  q7 : Eqn
  q7 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 158 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 624 W
  q11 : Eqn
  q11 = wE 625 W
  q12 : Eqn
  q12 = wE 1115 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 1116 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = wE 142 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = wE 36 W
  q22 : Eqn
  q22 = wE 37 W
  q23 : Eqn
  q23 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] part2: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-part2 : ⟪ (ℓ "丠丠丠临丠丠乀中乏丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丠丠临丠临临乏丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乀中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀丠丠临丠临临丹乄且乄且丧丧丧並乇且丶丶丶丶丶丶丽丽丽乔丽丽並丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-part2 = derive (ℓ "丠丠丠临丠丠乀中乏丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丠丠临丠临临乏丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乀中中中乑中中") (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀丠丠临丠临临丹乄且乄且丧丧丧並乇且丶丶丶丶丶丶丽丽丽乔丽丽並丹丧丧乄丧乄乄")
  (rw 10 q1 ∷
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
   re 13 3 (ℓ "乑") ∷
   rw 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
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
   rw⁻ 24 q3 ∷
   rw⁻ 25 q3 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q3 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw 30 q5 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 52 q1 ∷
   re 53 3 (ℓ "乑") ∷
   re 53 1 (ℓ "乏丼临丼乏") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乀") ∷
   rw 56 q6 ∷
   rw 55 q7 ∷
   rw 54 q8 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 53 q5 ∷
   re 54 5 (ℓ "乑") ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw 56 q5 ∷
   re 52 3 (ℓ "乀") ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 51 q1 ∷
   re 52 3 (ℓ "乑") ∷
   re 52 1 (ℓ "乏丼临丼乏") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "乀") ∷
   rw 55 q6 ∷
   rw 54 q7 ∷
   rw 53 q8 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 52 q5 ∷
   re 53 5 (ℓ "乑") ∷
   re 53 1 (ℓ "乏乄乏") ∷
   rw 55 q5 ∷
   re 51 3 (ℓ "乀") ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 50 q1 ∷
   re 51 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "乀") ∷
   rw 54 q6 ∷
   rw 53 q9 ∷
   rw 52 q8 ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 51 q5 ∷
   re 52 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q5 ∷
   re 50 3 (ℓ "乀") ∷
   re 50 1 (ℓ "乏丹乏") ∷
   rw 49 q1 ∷
   re 50 3 (ℓ "乑") ∷
   re 50 1 (ℓ "乏丼临丼乏") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乀") ∷
   rw 53 q6 ∷
   rw 52 q7 ∷
   rw 51 q8 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 50 q5 ∷
   re 51 5 (ℓ "乑") ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q5 ∷
   re 49 3 (ℓ "乀") ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 48 q1 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "乀") ∷
   rw 52 q6 ∷
   rw 51 q9 ∷
   rw 50 q8 ∷
   re 50 1 (ℓ "乏丹乏") ∷
   rw 49 q5 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q5 ∷
   re 48 3 (ℓ "乀") ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 47 q1 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乀") ∷
   rw 51 q6 ∷
   rw 50 q9 ∷
   rw 49 q8 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 48 q5 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q10 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q1 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "乀") ∷
   rw 49 q6 ∷
   rw 48 q9 ∷
   rw 47 q8 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 46 q5 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q5 ∷
   re 45 3 (ℓ "乀") ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q1 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乀") ∷
   rw 48 q6 ∷
   rw 47 q9 ∷
   rw 46 q8 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q5 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q5 ∷
   re 44 3 (ℓ "乀") ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q1 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q6 ∷
   rw 46 q9 ∷
   rw 45 q8 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q5 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q5 ∷
   re 43 3 (ℓ "乀") ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q1 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q6 ∷
   rw 45 q9 ∷
   rw 44 q8 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q5 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q5 ∷
   re 42 3 (ℓ "乀") ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q1 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "乀") ∷
   rw 45 q6 ∷
   rw 44 q9 ∷
   rw 43 q8 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q5 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q5 ∷
   re 41 3 (ℓ "乀") ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q1 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乀") ∷
   rw 44 q6 ∷
   rw 43 q9 ∷
   rw 42 q8 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q5 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q5 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q11 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q1 ∷
   re 39 3 (ℓ "乑") ∷
   re 39 1 (ℓ "乏丼临丼乏") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乀") ∷
   rw 42 q6 ∷
   rw 41 q7 ∷
   rw 40 q8 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q5 ∷
   re 40 5 (ℓ "乑") ∷
   re 40 1 (ℓ "乏乄乏") ∷
   rw 42 q5 ∷
   re 38 3 (ℓ "乀") ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q1 ∷
   re 38 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乀") ∷
   rw 41 q6 ∷
   rw 40 q9 ∷
   rw 39 q8 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q5 ∷
   re 39 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q5 ∷
   re 37 3 (ℓ "乀") ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q1 ∷
   re 37 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "乀") ∷
   rw 40 q6 ∷
   rw 39 q9 ∷
   rw 38 q8 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q5 ∷
   re 38 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q5 ∷
   re 36 3 (ℓ "乀") ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q6 ∷
   rw 38 q9 ∷
   rw 37 q8 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q5 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q11 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q1 ∷
   re 34 3 (ℓ "乑") ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q6 ∷
   rw 36 q7 ∷
   rw 35 q8 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q5 ∷
   re 35 5 (ℓ "乑") ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q5 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q11 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q1 ∷
   re 32 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏丼临丼乏") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q6 ∷
   rw 34 q7 ∷
   rw 33 q8 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q5 ∷
   re 33 5 (ℓ "乑") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q5 ∷
   re 31 3 (ℓ "乀") ∷
   rw 30 q10 ∷
   rw 31 q1 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q5 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q3 ∷
   rw 24 q3 ∷
   rw 25 q12 ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乀") ∷
   rw⁻ 25 q3 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q4 ∷
   rw 31 q5 ∷
   rw 60 q13 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q14 ∷
   rw 60 q15 ∷
   rw⁻ 59 q14 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q14 ∷
   rw 59 q15 ∷
   rw⁻ 58 q14 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw⁻ 59 q14 ∷
   rw 58 q16 ∷
   rw⁻ 57 q14 ∷
   re 58 3 (ℓ "乔") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q14 ∷
   rw 57 q15 ∷
   rw⁻ 56 q14 ∷
   re 57 3 (ℓ "丽") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q14 ∷
   rw 56 q15 ∷
   rw⁻ 55 q14 ∷
   re 56 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q14 ∷
   rw 55 q15 ∷
   rw⁻ 54 q14 ∷
   re 55 3 (ℓ "丽") ∷
   rw 53 q16 ∷
   rw 52 q16 ∷
   rw 51 q15 ∷
   rw 50 q16 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 49 q17 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q14 ∷
   rw 49 q18 ∷
   rw 50 q14 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q14 ∷
   rw 50 q18 ∷
   rw 51 q14 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q14 ∷
   rw 51 q18 ∷
   rw 52 q14 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏乇乏") ∷
   rw 51 q14 ∷
   rw 52 q19 ∷
   rw 53 q14 ∷
   re 51 3 (ℓ "乑") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q14 ∷
   rw 53 q18 ∷
   rw 54 q14 ∷
   re 52 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q14 ∷
   rw 54 q18 ∷
   rw 55 q14 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q18 ∷
   rw 55 q18 ∷
   rw 56 q19 ∷
   rw 57 q18 ∷
   rw 58 q19 ∷
   rw 59 q19 ∷
   rw 60 q20 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q1 ∷
   re 48 3 (ℓ "乀") ∷
   rw 48 q21 ∷
   rw⁻ 49 q9 ∷
   rw 50 q22 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 53 q5 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q1 ∷
   re 49 3 (ℓ "乀") ∷
   rw 49 q21 ∷
   rw⁻ 50 q9 ∷
   rw 51 q22 ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 54 q5 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q1 ∷
   re 50 3 (ℓ "乀") ∷
   rw 50 q21 ∷
   rw⁻ 51 q9 ∷
   rw 52 q22 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 55 q5 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼临丼乏") ∷
   rw 50 q1 ∷
   re 51 3 (ℓ "乀") ∷
   rw 51 q21 ∷
   rw⁻ 52 q7 ∷
   rw 53 q22 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 56 q5 ∷
   re 50 5 (ℓ "乑") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q1 ∷
   re 52 3 (ℓ "乀") ∷
   rw 52 q21 ∷
   rw⁻ 53 q9 ∷
   rw 54 q22 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 57 q5 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q1 ∷
   re 53 3 (ℓ "乀") ∷
   rw 53 q21 ∷
   rw⁻ 54 q9 ∷
   rw 55 q22 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 58 q5 ∷
   re 52 5 (ℓ "中") ∷
   rw 53 q13 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q14 ∷
   rw 53 q15 ∷
   rw⁻ 52 q14 ∷
   re 53 3 (ℓ "丽") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q14 ∷
   rw 52 q15 ∷
   rw⁻ 51 q14 ∷
   re 52 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏乄乏") ∷
   rw⁻ 52 q14 ∷
   rw 51 q16 ∷
   rw⁻ 50 q14 ∷
   re 51 3 (ℓ "乔") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q14 ∷
   rw 50 q15 ∷
   rw⁻ 49 q14 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q14 ∷
   rw 49 q15 ∷
   rw⁻ 48 q14 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q14 ∷
   rw 48 q15 ∷
   rw⁻ 47 q14 ∷
   re 48 3 (ℓ "丽") ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw⁻ 40 q23 ∷
   rw 39 q16 ∷ []) Eq.refl
