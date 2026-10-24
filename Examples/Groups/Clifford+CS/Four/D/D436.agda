{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D436 (W : Ws) where

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
  q2 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 464 W
  q6 : Eqn
  q6 = wE 1125 W
  q7 : Eqn
  q7 = wE 151 W
  q8 : Eqn
  q8 = wE 157 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 158 W
  q11 : Eqn
  q11 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 589 W
  q13 : Eqn
  q13 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q14 : Eqn
  q14 = wE 1126 W
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
  q20 = wE 1175 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 142 W
  q23 : Eqn
  q23 = wE 31 W
  q24 : Eqn
  q24 = wE 36 W
  q25 : Eqn
  q25 = wE 37 W
  q26 : Eqn
  q26 = wE 883 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02] part0: 500 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part0 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠丹丠丠丠临丠丠乀中中中中中中乑业中中中並乏丶乏丽丽丽丽丽丶丶丶乇且丶丶丶丶丶丶並乀中中中乑中中丹丧丧乄丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part0 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧") (ℓ "丠丠临丠丹丠丠丠临丠丠乀中中中中中中乑业中中中並乏丶乏丽丽丽丽丽丶丶丶乇且丶丶丶丶丶丶並乀中中中乑中中丹丧丧乄丧")
  (rw 35 q1 ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q2 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q4 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q4 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丧乏") ∷
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
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q4 ∷
   rw 14 q5 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q4 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q4 ∷
   rw 5 q2 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q2 ∷
   rw 1 q2 ∷
   rw 0 q2 ∷
   rw 1 q6 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q2 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乀") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q7 ∷
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
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "乑") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q4 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q8 ∷
   rw 36 q9 ∷
   rw 35 q10 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q4 ∷
   re 35 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q8 ∷
   rw 35 q9 ∷
   rw 34 q10 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q4 ∷
   re 34 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼临丼乏") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q8 ∷
   rw 34 q11 ∷
   rw 33 q10 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q4 ∷
   re 33 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q8 ∷
   rw 33 q9 ∷
   rw 32 q10 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q4 ∷
   re 32 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q8 ∷
   rw 32 q9 ∷
   rw 31 q10 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q8 ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "中") ∷
   rw 28 q12 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乀") ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q8 ∷
   rw 28 q9 ∷
   rw 27 q10 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q4 ∷
   re 26 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乀") ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 24 q4 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乀") ∷
   rw 26 q8 ∷
   rw 25 q9 ∷
   rw 24 q10 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q4 ∷
   re 24 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "乀") ∷
   rw 25 q8 ∷
   rw 24 q9 ∷
   rw 23 q10 ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 22 q4 ∷
   re 23 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乀") ∷
   rw 24 q8 ∷
   rw 23 q9 ∷
   rw 22 q10 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 21 q4 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乀") ∷
   rw 23 q8 ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 20 q4 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乀") ∷
   rw 22 q8 ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   re 20 1 (ℓ "乏丹乏") ∷
   rw 19 q4 ∷
   re 20 5 (ℓ "中") ∷
   rw⁻ 18 q13 ∷
   re 17 1 (ℓ "乏丼临丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "乀") ∷
   rw 20 q8 ∷
   rw 19 q11 ∷
   rw 18 q10 ∷
   re 18 1 (ℓ "乏丹乏") ∷
   rw 17 q4 ∷
   re 18 5 (ℓ "乑") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "乀") ∷
   rw 19 q8 ∷
   rw 18 q9 ∷
   rw 17 q10 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q4 ∷
   re 17 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乀") ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   re 16 1 (ℓ "乏丹乏") ∷
   rw 15 q4 ∷
   re 16 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乀") ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   re 15 1 (ℓ "乏丹乏") ∷
   rw 14 q4 ∷
   re 15 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乀") ∷
   rw 16 q8 ∷
   rw 15 q9 ∷
   rw 14 q10 ∷
   re 14 1 (ℓ "乏丹乏") ∷
   rw 13 q4 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乀") ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏丹乏") ∷
   rw 12 q4 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乀") ∷
   rw 14 q8 ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   re 12 1 (ℓ "乏丹乏") ∷
   rw 11 q4 ∷
   re 12 5 (ℓ "中") ∷
   rw 10 q12 ∷
   rw 4 q14 ∷
   rw 47 q15 ∷
   rw 46 q16 ∷
   rw 45 q16 ∷
   rw 44 q16 ∷
   rw 43 q16 ∷
   rw 42 q16 ∷
   rw 41 q16 ∷
   rw⁻ 40 q17 ∷
   rw 39 q18 ∷
   rw 38 q16 ∷
   rw 37 q16 ∷
   rw 36 q16 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q19 ∷
   rw 36 q16 ∷
   rw⁻ 35 q19 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q19 ∷
   rw 35 q16 ∷
   rw⁻ 34 q19 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q19 ∷
   rw 34 q18 ∷
   rw⁻ 33 q19 ∷
   re 34 3 (ℓ "乔") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q19 ∷
   rw 33 q16 ∷
   rw⁻ 32 q19 ∷
   re 33 3 (ℓ "丽") ∷
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
   rw 31 q21 ∷
   rw 32 q21 ∷
   rw 33 q22 ∷
   rw 34 q17 ∷
   rw 35 q21 ∷
   rw 36 q21 ∷
   rw 37 q21 ∷
   rw 38 q21 ∷
   rw 39 q21 ∷
   rw 40 q21 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q19 ∷
   rw 42 q21 ∷
   rw 43 q19 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q19 ∷
   rw 43 q21 ∷
   rw 44 q19 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q19 ∷
   rw 44 q21 ∷
   rw 45 q19 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏乇乏") ∷
   rw 44 q19 ∷
   rw 45 q22 ∷
   rw 46 q19 ∷
   re 44 3 (ℓ "乑") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q19 ∷
   rw 46 q21 ∷
   rw 47 q19 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q19 ∷
   rw 47 q21 ∷
   rw 48 q19 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q23 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q24 ∷
   rw⁻ 30 q9 ∷
   rw 31 q25 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q24 ∷
   rw⁻ 31 q9 ∷
   rw 32 q25 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q24 ∷
   rw⁻ 32 q9 ∷
   rw 33 q25 ∷
   re 31 3 (ℓ "丧") ∷
   re 33 1 (ℓ "丼临丼") ∷
   rw 32 q24 ∷
   rw⁻ 33 q11 ∷
   rw 34 q25 ∷
   re 32 3 (ℓ "乄") ∷
   rw 33 q26 ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 34 q24 ∷
   rw⁻ 35 q9 ∷
   rw 36 q25 ∷
   re 34 3 (ℓ "丧") ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q24 ∷
   rw⁻ 36 q9 ∷
   rw 37 q25 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q24 ∷
   rw⁻ 37 q9 ∷
   rw 38 q25 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q24 ∷
   rw⁻ 38 q9 ∷
   rw 39 q25 ∷
   re 37 3 (ℓ "丧") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q24 ∷
   rw⁻ 39 q9 ∷
   rw 40 q25 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q24 ∷
   rw⁻ 40 q9 ∷
   rw 41 q25 ∷
   re 39 3 (ℓ "丧") ∷
   rw 40 q15 ∷
   rw 39 q16 ∷
   rw 38 q16 ∷
   rw 37 q16 ∷
   rw 36 q16 ∷
   rw 35 q16 ∷
   rw 34 q16 ∷
   rw⁻ 33 q17 ∷
   rw 32 q18 ∷
   rw 31 q16 ∷
   rw 30 q16 ∷
   rw 29 q16 ∷
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
   rw⁻ 23 q19 ∷ []) Eq.refl
