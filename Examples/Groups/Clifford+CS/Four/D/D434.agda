{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D434 (W : Ws) where

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
  q2 = wE 142 W
  q3 : Eqn
  q3 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 27 W
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = wE 36 W
  q7 : Eqn
  q7 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q8 : Eqn
  q8 = wE 37 W
  q9 : Eqn
  q9 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q10 : Eqn
  q10 = wE 883 W
  q11 : Eqn
  q11 = wE 1121 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 157 W
  q14 : Eqn
  q14 = wE 158 W
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = wE 589 W
  q17 : Eqn
  q17 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q18 : Eqn
  q18 = wE 1115 W
  q19 : Eqn
  q19 = wE 5 W
  q20 : Eqn
  q20 = wE 7 W
  q21 : Eqn
  q21 = wE 140 W
  q22 : Eqn
  q22 = wE 1173 W
  q23 : Eqn
  q23 = wE 1174 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02] part1: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part1 : ⟪ (ℓ "丠丠临丠丹丠丠临丠临临乀丧丧丧乄且丧丧丧丧丧丧並乔业乔业丽丽丽乔业丽丽丽丽丽丽並乀中中乑中乑乑丹丧丧乄丧") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丠丠临丠临临乀丧丧乄丧乑业乑业中中中乑业中中中乏丧乏並丽丽並乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part1 = derive (ℓ "丠丠临丠丹丠丠临丠临临乀丧丧丧乄且丧丧丧丧丧丧並乔业乔业丽丽丽乔业丽丽丽丽丽丽並乀中中乑中乑乑丹丧丧乄丧") (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丠丠临丠临临乀丧丧乄丧乑业乑业中中中乑业中中中乏丧乏並丽丽並乀中中乑中乑乑")
  (re 24 1 (ℓ "乏乇乏") ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乑") ∷
   rw 24 q3 ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乑") ∷
   rw 26 q3 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q1 ∷
   rw 28 q4 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q1 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q1 ∷
   rw 30 q4 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乑") ∷
   rw 31 q3 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q1 ∷
   rw 33 q4 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q1 ∷
   rw 34 q4 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q1 ∷
   rw 35 q4 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q1 ∷
   rw 36 q4 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q1 ∷
   rw 37 q4 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q1 ∷
   rw 38 q4 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q5 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 11 q6 ∷
   rw⁻ 12 q7 ∷
   rw 13 q8 ∷
   re 11 3 (ℓ "丧") ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q6 ∷
   rw⁻ 13 q7 ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "丧") ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q6 ∷
   rw⁻ 14 q7 ∷
   rw 15 q8 ∷
   re 13 3 (ℓ "丧") ∷
   re 15 1 (ℓ "丼临丼") ∷
   rw 14 q6 ∷
   rw⁻ 15 q9 ∷
   rw 16 q8 ∷
   re 14 3 (ℓ "乄") ∷
   rw 15 q10 ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 16 q6 ∷
   rw⁻ 17 q7 ∷
   rw 18 q8 ∷
   re 16 3 (ℓ "丧") ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q6 ∷
   rw⁻ 18 q7 ∷
   rw 19 q8 ∷
   re 17 3 (ℓ "丧") ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q6 ∷
   rw⁻ 19 q7 ∷
   rw 20 q8 ∷
   re 18 3 (ℓ "丧") ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q6 ∷
   rw⁻ 20 q7 ∷
   rw 21 q8 ∷
   re 19 3 (ℓ "丧") ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q6 ∷
   rw⁻ 21 q7 ∷
   rw 22 q8 ∷
   re 20 3 (ℓ "丧") ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q6 ∷
   rw⁻ 22 q7 ∷
   rw 23 q8 ∷
   re 21 3 (ℓ "丧") ∷
   rw 5 q11 ∷
   re 44 1 (ℓ "乏丼临丼乏") ∷
   rw 50 q12 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q13 ∷
   rw 46 q9 ∷
   rw 45 q14 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q15 ∷
   re 45 5 (ℓ "乑") ∷
   re 43 1 (ℓ "乏丼临丼乏") ∷
   rw 49 q12 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q13 ∷
   rw 45 q9 ∷
   rw 44 q14 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q15 ∷
   re 44 5 (ℓ "乑") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q12 ∷
   re 46 3 (ℓ "乀") ∷
   rw 45 q13 ∷
   rw 44 q7 ∷
   rw 43 q14 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q15 ∷
   re 43 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼临丼乏") ∷
   rw 47 q12 ∷
   re 45 3 (ℓ "乀") ∷
   rw 44 q13 ∷
   rw 43 q9 ∷
   rw 42 q14 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q15 ∷
   re 42 5 (ℓ "乑") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q12 ∷
   re 44 3 (ℓ "乀") ∷
   rw 43 q13 ∷
   rw 42 q7 ∷
   rw 41 q14 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q15 ∷
   re 41 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q12 ∷
   re 43 3 (ℓ "乀") ∷
   rw 42 q13 ∷
   rw 41 q7 ∷
   rw 40 q14 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q15 ∷
   re 40 5 (ℓ "中") ∷
   rw 38 q16 ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q12 ∷
   re 41 3 (ℓ "乀") ∷
   rw 40 q13 ∷
   rw 39 q7 ∷
   rw 38 q14 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q15 ∷
   re 38 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q12 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q13 ∷
   rw 38 q7 ∷
   rw 37 q14 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q15 ∷
   re 37 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q12 ∷
   re 39 3 (ℓ "乀") ∷
   rw 38 q13 ∷
   rw 37 q7 ∷
   rw 36 q14 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q15 ∷
   re 36 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q12 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q13 ∷
   rw 36 q7 ∷
   rw 35 q14 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q15 ∷
   re 35 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q12 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q13 ∷
   rw 35 q7 ∷
   rw 34 q14 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q15 ∷
   re 34 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q12 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q13 ∷
   rw 34 q7 ∷
   rw 33 q14 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q15 ∷
   re 33 5 (ℓ "中") ∷
   rw⁻ 31 q17 ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q12 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q13 ∷
   rw 32 q9 ∷
   rw 31 q14 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q15 ∷
   re 31 5 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q12 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q13 ∷
   rw 31 q7 ∷
   rw 30 q14 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q15 ∷
   re 30 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q12 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q13 ∷
   rw 30 q7 ∷
   rw 29 q14 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q15 ∷
   re 29 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q12 ∷
   re 31 3 (ℓ "乀") ∷
   rw 30 q13 ∷
   rw 29 q7 ∷
   rw 28 q14 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q15 ∷
   re 28 5 (ℓ "中") ∷
   rw⁻ 26 q17 ∷
   re 25 1 (ℓ "乏丼临丼乏") ∷
   rw 31 q12 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q13 ∷
   rw 27 q9 ∷
   rw 26 q14 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q15 ∷
   re 26 5 (ℓ "乑") ∷
   rw⁻ 24 q17 ∷
   re 23 1 (ℓ "乏丼临丼乏") ∷
   rw 29 q12 ∷
   re 27 3 (ℓ "乀") ∷
   rw 26 q13 ∷
   rw 25 q9 ∷
   rw 24 q14 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q15 ∷
   re 24 5 (ℓ "乑") ∷
   rw 22 q16 ∷
   rw 16 q18 ∷
   rw 50 q19 ∷
   rw 49 q20 ∷
   rw 48 q21 ∷
   rw 47 q20 ∷
   rw 46 q20 ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw⁻ 47 q1 ∷
   rw 46 q21 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (ℓ "乔") ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw⁻ 46 q1 ∷
   rw 45 q21 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (ℓ "乔") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q1 ∷
   rw 44 q20 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw⁻ 44 q1 ∷
   rw 43 q21 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (ℓ "乔") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q1 ∷
   rw 42 q20 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q1 ∷
   rw 41 q20 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q22 ∷
   rw 40 q4 ∷
   rw 41 q4 ∷
   rw 42 q2 ∷
   rw 43 q4 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q1 ∷
   rw 45 q4 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q1 ∷
   rw 46 q4 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏乇乏") ∷
   rw 46 q1 ∷
   rw 47 q2 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "乑") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q1 ∷
   rw 48 q4 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏乇乏") ∷
   rw 48 q1 ∷
   rw 49 q2 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乑") ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q1 ∷
   rw 50 q2 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q5 ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q6 ∷
   rw⁻ 40 q7 ∷
   rw 41 q8 ∷
   re 39 3 (ℓ "丧") ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 40 q6 ∷
   rw⁻ 41 q7 ∷
   rw 42 q8 ∷
   re 40 3 (ℓ "丧") ∷
   re 42 1 (ℓ "丼临丼") ∷
   rw 41 q6 ∷
   rw⁻ 42 q9 ∷
   rw 43 q8 ∷
   re 41 3 (ℓ "乄") ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q6 ∷
   rw⁻ 43 q7 ∷
   rw 44 q8 ∷
   re 42 3 (ℓ "丧") ∷
   rw 43 q19 ∷
   rw 42 q20 ∷
   rw 41 q21 ∷
   rw 40 q20 ∷
   rw 39 q20 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q1 ∷
   rw 39 q20 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q1 ∷
   rw 38 q20 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q1 ∷
   rw 37 q20 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q1 ∷
   rw 36 q20 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q1 ∷
   rw 35 q20 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q1 ∷
   rw 34 q20 ∷
   rw⁻ 33 q1 ∷
   re 34 3 (ℓ "丽") ∷
   rw⁻ 32 q3 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw⁻ 33 q1 ∷
   rw 32 q21 ∷
   rw⁻ 31 q1 ∷
   re 32 3 (ℓ "乔") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q1 ∷
   rw 31 q20 ∷
   rw⁻ 30 q1 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q1 ∷
   rw 30 q20 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q1 ∷
   rw 29 q20 ∷
   rw⁻ 28 q1 ∷
   re 29 3 (ℓ "丽") ∷
   rw⁻ 27 q3 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw⁻ 28 q1 ∷
   rw 27 q21 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (ℓ "乔") ∷
   rw⁻ 25 q3 ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw⁻ 26 q1 ∷
   rw 25 q21 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (ℓ "乔") ∷
   rw 25 q23 ∷
   rw 24 q4 ∷
   rw 25 q4 ∷
   rw 26 q2 ∷
   rw 27 q4 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q3 ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乑") ∷
   rw 31 q3 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q1 ∷
   rw 33 q4 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q1 ∷
   rw 34 q4 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q1 ∷
   rw 35 q4 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q1 ∷
   rw 36 q2 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q3 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q1 ∷
   rw 38 q4 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q1 ∷
   rw 39 q4 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q1 ∷
   rw 40 q4 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q1 ∷
   rw 41 q4 ∷
   rw 42 q1 ∷ []) Eq.refl
