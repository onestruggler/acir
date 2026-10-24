{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D396 (W : Ws) where

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
  q2 = wE 157 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q4 : Eqn
  q4 = wE 158 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 625 W
  q7 : Eqn
  q7 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 624 W
  q9 : Eqn
  q9 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = wE 1115 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 7 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 1122 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = wE 36 W
  q21 : Eqn
  q21 = wE 37 W
  q22 : Eqn
  q22 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q23 : Eqn
  q23 = wE 1123 W
  q24 : Eqn
  q24 = wE 1124 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03] part2: 311 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part2 : ⟪ (ℓ "丠丠临丠乀中中中乑业中中中中中中丠丠临丠临临丹乄且乄且丧乏乏丧乏丹乏丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄中中乑中") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part2 = derive (ℓ "丠丠临丠乀中中中乑业中中中中中中丠丠临丠临临丹乄且乄且丧乏乏丧乏丹乏丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄中中乑中") (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q5 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   re 28 3 (ℓ "乀") ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q5 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   re 27 3 (ℓ "乀") ∷
   rw 26 q6 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼临丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q2 ∷
   rw 28 q7 ∷
   rw 27 q4 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q5 ∷
   re 27 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q5 ∷
   re 25 3 (ℓ "乀") ∷
   rw 24 q6 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼临丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乀") ∷
   rw 27 q2 ∷
   rw 26 q7 ∷
   rw 25 q4 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 24 q5 ∷
   re 25 5 (ℓ "乑") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q5 ∷
   re 23 3 (ℓ "乀") ∷
   rw 22 q8 ∷
   rw 23 q1 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q5 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q9 ∷
   rw 17 q10 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乀") ∷
   rw⁻ 17 q10 ∷
   rw⁻ 18 q10 ∷
   rw⁻ 19 q9 ∷
   rw⁻ 20 q10 ∷
   rw⁻ 21 q9 ∷
   rw⁻ 22 q9 ∷
   rw 23 q5 ∷
   rw 50 q12 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q13 ∷
   rw 50 q14 ∷
   rw⁻ 49 q13 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw⁻ 50 q13 ∷
   rw 49 q15 ∷
   rw⁻ 48 q13 ∷
   re 49 3 (ℓ "乔") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q13 ∷
   rw 48 q14 ∷
   rw⁻ 47 q13 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q13 ∷
   rw 47 q14 ∷
   rw⁻ 46 q13 ∷
   re 47 3 (ℓ "丽") ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q14 ∷
   rw 42 q15 ∷
   rw 41 q14 ∷
   rw 40 q14 ∷
   rw 41 q16 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q13 ∷
   rw 41 q17 ∷
   rw 42 q13 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q13 ∷
   rw 42 q17 ∷
   rw 43 q13 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏乇乏") ∷
   rw 42 q13 ∷
   rw 43 q18 ∷
   rw 44 q13 ∷
   re 42 3 (ℓ "乑") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q13 ∷
   rw 44 q17 ∷
   rw 45 q13 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q17 ∷
   rw 45 q17 ∷
   rw 46 q18 ∷
   rw 47 q17 ∷
   rw 48 q18 ∷
   rw 49 q18 ∷
   rw 50 q19 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q1 ∷
   re 40 3 (ℓ "乀") ∷
   rw 40 q20 ∷
   rw⁻ 41 q3 ∷
   rw 42 q21 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 45 q5 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q1 ∷
   re 41 3 (ℓ "乀") ∷
   rw 41 q20 ∷
   rw⁻ 42 q3 ∷
   rw 43 q21 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 46 q5 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼临丼乏") ∷
   rw 41 q1 ∷
   re 42 3 (ℓ "乀") ∷
   rw 42 q20 ∷
   rw⁻ 43 q7 ∷
   rw 44 q21 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 47 q5 ∷
   re 41 5 (ℓ "乑") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q1 ∷
   re 43 3 (ℓ "乀") ∷
   rw 43 q20 ∷
   rw⁻ 44 q3 ∷
   rw 45 q21 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 48 q5 ∷
   re 42 5 (ℓ "中") ∷
   rw 43 q12 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q13 ∷
   rw 43 q14 ∷
   rw⁻ 42 q13 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏乄乏") ∷
   rw⁻ 43 q13 ∷
   rw 42 q15 ∷
   rw⁻ 41 q13 ∷
   re 42 3 (ℓ "乔") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q13 ∷
   rw 41 q14 ∷
   rw⁻ 40 q13 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q13 ∷
   rw 40 q14 ∷
   rw⁻ 39 q13 ∷
   re 40 3 (ℓ "丽") ∷
   rw 38 q14 ∷
   rw 37 q14 ∷
   rw 36 q14 ∷
   rw 35 q14 ∷
   rw 34 q14 ∷
   rw 33 q14 ∷
   rw⁻ 32 q22 ∷
   rw 31 q15 ∷
   rw 30 q14 ∷
   rw 29 q14 ∷
   rw 28 q14 ∷
   rw⁻ 27 q22 ∷
   rw 26 q15 ∷
   rw⁻ 25 q22 ∷
   rw 24 q15 ∷
   rw 25 q23 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q13 ∷
   rw 25 q17 ∷
   rw 26 q13 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q13 ∷
   rw 26 q17 ∷
   rw 27 q13 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q13 ∷
   rw 27 q18 ∷
   rw 28 q13 ∷
   re 26 3 (ℓ "乑") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q13 ∷
   rw 28 q17 ∷
   rw 29 q13 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q18 ∷
   rw 29 q22 ∷
   rw 30 q18 ∷
   rw 31 q22 ∷
   rw 32 q17 ∷
   rw 33 q17 ∷
   rw 34 q17 ∷
   rw 35 q18 ∷
   rw 36 q22 ∷
   rw 37 q17 ∷
   rw 38 q17 ∷
   rw 39 q17 ∷
   rw 40 q17 ∷
   rw 41 q17 ∷
   rw 42 q17 ∷
   rw 43 q19 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "乀") ∷
   rw 24 q20 ∷
   rw⁻ 25 q3 ∷
   rw 26 q21 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 29 q5 ∷
   re 23 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 25 3 (ℓ "乀") ∷
   rw 25 q20 ∷
   rw⁻ 26 q3 ∷
   rw 27 q21 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 30 q5 ∷
   re 24 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼临丼乏") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "乀") ∷
   rw 26 q20 ∷
   rw⁻ 27 q7 ∷
   rw 28 q21 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 31 q5 ∷
   re 25 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "乀") ∷
   rw 27 q20 ∷
   rw⁻ 28 q3 ∷
   rw 29 q21 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q5 ∷
   re 26 5 (ℓ "中") ∷
   rw 27 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q5 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q5 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q5 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q5 ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   rw 17 q10 ∷
   rw 18 q24 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乑") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw⁻ 21 q10 ∷
   rw⁻ 22 q10 ∷
   rw⁻ 23 q9 ∷
   rw⁻ 24 q10 ∷
   rw⁻ 25 q9 ∷
   rw⁻ 26 q9 ∷
   rw 27 q5 ∷ []) Eq.refl
