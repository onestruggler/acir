{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D391 (W : Ws) where

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
  q2 = wE 36 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q4 : Eqn
  q4 = wE 37 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q7 : Eqn
  q7 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q14 : Eqn
  q14 = wE 964 W
  q15 : Eqn
  q15 = wE 27 W
  q16 : Eqn
  q16 = wE 142 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 464 W
  q19 : Eqn
  q19 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = wE 843 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] part1: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-part1 : ⟪ (ℓ "丠丠丠临丠丠乀丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中丹乏丼丠丼乏中中乑业中中中中中中中中中丧丧乄丧乄乄乀中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丠丠丠临丠丠乀中乏丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丠丠临丠临临乏丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-part1 = derive (ℓ "丠丠丠临丠丠乀丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中丹乏丼丠丼乏中中乑业中中中中中中中中中丧丧乄丧乄乄乀中中中乑中中") (ℓ "丠丠丠临丠丠乀中乏丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丠丠临丠临临乏丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乀中中中乑中中")
  (rw 32 q1 ∷
   re 33 3 (ℓ "乀") ∷
   rw 33 q2 ∷
   rw⁻ 34 q3 ∷
   rw 35 q4 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 38 q5 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 34 3 (ℓ "乀") ∷
   rw 34 q2 ∷
   rw⁻ 35 q3 ∷
   rw 36 q4 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q5 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 35 3 (ℓ "乀") ∷
   rw 35 q2 ∷
   rw⁻ 36 q3 ∷
   rw 37 q4 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q5 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "乀") ∷
   rw 36 q2 ∷
   rw⁻ 37 q6 ∷
   rw 38 q4 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 41 q5 ∷
   re 35 5 (ℓ "乑") ∷
   rw 36 q7 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 38 3 (ℓ "乀") ∷
   rw 38 q2 ∷
   rw⁻ 39 q3 ∷
   rw 40 q4 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 43 q5 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q1 ∷
   re 39 3 (ℓ "乀") ∷
   rw 39 q2 ∷
   rw⁻ 40 q3 ∷
   rw 41 q4 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 44 q5 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q1 ∷
   re 40 3 (ℓ "乀") ∷
   rw 40 q2 ∷
   rw⁻ 41 q3 ∷
   rw 42 q4 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 45 q5 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q1 ∷
   re 41 3 (ℓ "乀") ∷
   rw 41 q2 ∷
   rw⁻ 42 q3 ∷
   rw 43 q4 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 46 q5 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q1 ∷
   re 42 3 (ℓ "乀") ∷
   rw 42 q2 ∷
   rw⁻ 43 q3 ∷
   rw 44 q4 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 47 q5 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q1 ∷
   re 43 3 (ℓ "乀") ∷
   rw 43 q2 ∷
   rw⁻ 44 q3 ∷
   rw 45 q4 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 48 q5 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q1 ∷
   re 44 3 (ℓ "乀") ∷
   rw 44 q2 ∷
   rw⁻ 45 q3 ∷
   rw 46 q4 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 49 q5 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q1 ∷
   re 45 3 (ℓ "乀") ∷
   rw 45 q2 ∷
   rw⁻ 46 q3 ∷
   rw 47 q4 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 50 q5 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q1 ∷
   re 46 3 (ℓ "乀") ∷
   rw 46 q2 ∷
   rw⁻ 47 q3 ∷
   rw 48 q4 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 51 q5 ∷
   re 45 5 (ℓ "中") ∷
   rw 46 q8 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q9 ∷
   rw 46 q10 ∷
   rw⁻ 45 q9 ∷
   re 46 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q9 ∷
   rw 45 q10 ∷
   rw⁻ 44 q9 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q9 ∷
   rw 44 q10 ∷
   rw⁻ 43 q9 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q9 ∷
   rw 43 q10 ∷
   rw⁻ 42 q9 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q9 ∷
   rw 42 q10 ∷
   rw⁻ 41 q9 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q9 ∷
   rw 41 q10 ∷
   rw⁻ 40 q9 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q9 ∷
   rw 40 q10 ∷
   rw⁻ 39 q9 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q9 ∷
   rw 39 q10 ∷
   rw⁻ 38 q9 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q9 ∷
   rw 38 q10 ∷
   rw⁻ 37 q9 ∷
   re 38 3 (ℓ "丽") ∷
   rw⁻ 36 q11 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q9 ∷
   rw 36 q12 ∷
   rw⁻ 35 q9 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q9 ∷
   rw 35 q10 ∷
   rw⁻ 34 q9 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q9 ∷
   rw 34 q10 ∷
   rw⁻ 33 q9 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q9 ∷
   rw 33 q10 ∷
   rw⁻ 32 q9 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q9 ∷
   rw 32 q10 ∷
   rw⁻ 31 q9 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q9 ∷
   rw 31 q10 ∷
   rw⁻ 30 q9 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q9 ∷
   rw 30 q10 ∷
   rw⁻ 29 q9 ∷
   re 30 3 (ℓ "丽") ∷
   rw 28 q10 ∷
   rw 27 q10 ∷
   rw 26 q10 ∷
   rw 25 q10 ∷
   rw 24 q10 ∷
   rw 23 q10 ∷
   rw⁻ 22 q13 ∷
   rw 21 q12 ∷
   rw 20 q10 ∷
   rw 19 q10 ∷
   rw 18 q10 ∷
   rw⁻ 17 q13 ∷
   rw 16 q12 ∷
   rw⁻ 15 q13 ∷
   rw 14 q12 ∷
   rw 15 q14 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q9 ∷
   rw 15 q15 ∷
   rw 16 q9 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q9 ∷
   rw 16 q15 ∷
   rw 17 q9 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q9 ∷
   rw 17 q15 ∷
   rw 18 q9 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q9 ∷
   rw 18 q15 ∷
   rw 19 q9 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q9 ∷
   rw 19 q15 ∷
   rw 20 q9 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q9 ∷
   rw 20 q15 ∷
   rw 21 q9 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q9 ∷
   rw 21 q16 ∷
   rw 22 q9 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q11 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q9 ∷
   rw 23 q15 ∷
   rw 24 q9 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q9 ∷
   rw 24 q15 ∷
   rw 25 q9 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q9 ∷
   rw 25 q15 ∷
   rw 26 q9 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q9 ∷
   rw 26 q15 ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q9 ∷
   rw 27 q15 ∷
   rw 28 q9 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q9 ∷
   rw 28 q15 ∷
   rw 29 q9 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q9 ∷
   rw 29 q15 ∷
   rw 30 q9 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q9 ∷
   rw 30 q15 ∷
   rw 31 q9 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q9 ∷
   rw 31 q15 ∷
   rw 32 q9 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q16 ∷
   rw 32 q13 ∷
   rw 33 q16 ∷
   rw 34 q13 ∷
   rw 35 q15 ∷
   rw 36 q15 ∷
   rw 37 q15 ∷
   rw 38 q16 ∷
   rw 39 q13 ∷
   rw 40 q15 ∷
   rw 41 q15 ∷
   rw 42 q15 ∷
   rw 43 q15 ∷
   rw 44 q15 ∷
   rw 45 q15 ∷
   rw 46 q17 ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q1 ∷
   re 14 3 (ℓ "乀") ∷
   rw 14 q2 ∷
   rw⁻ 15 q3 ∷
   rw 16 q4 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 19 q5 ∷
   re 13 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q1 ∷
   re 15 3 (ℓ "乀") ∷
   rw 15 q2 ∷
   rw⁻ 16 q3 ∷
   rw 17 q4 ∷
   re 18 1 (ℓ "乏丹乏") ∷
   rw 20 q5 ∷
   re 14 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q1 ∷
   re 16 3 (ℓ "乀") ∷
   rw 16 q2 ∷
   rw⁻ 17 q3 ∷
   rw 18 q4 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 21 q5 ∷
   re 15 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q1 ∷
   re 17 3 (ℓ "乀") ∷
   rw 17 q2 ∷
   rw⁻ 18 q3 ∷
   rw 19 q4 ∷
   re 20 1 (ℓ "乏丹乏") ∷
   rw 22 q5 ∷
   re 16 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 18 3 (ℓ "乀") ∷
   rw 18 q2 ∷
   rw⁻ 19 q3 ∷
   rw 20 q4 ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 23 q5 ∷
   re 17 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 19 3 (ℓ "乀") ∷
   rw 19 q2 ∷
   rw⁻ 20 q3 ∷
   rw 21 q4 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q5 ∷
   re 18 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q1 ∷
   re 20 3 (ℓ "乀") ∷
   rw 20 q2 ∷
   rw⁻ 21 q6 ∷
   rw 22 q4 ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 25 q5 ∷
   re 19 5 (ℓ "乑") ∷
   rw 20 q7 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "乀") ∷
   rw 22 q2 ∷
   rw⁻ 23 q3 ∷
   rw 24 q4 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 27 q5 ∷
   re 21 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "乀") ∷
   rw 23 q2 ∷
   rw⁻ 24 q3 ∷
   rw 25 q4 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 28 q5 ∷
   re 22 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "乀") ∷
   rw 24 q2 ∷
   rw⁻ 25 q3 ∷
   rw 26 q4 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 29 q5 ∷
   re 23 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 25 3 (ℓ "乀") ∷
   rw 25 q2 ∷
   rw⁻ 26 q3 ∷
   rw 27 q4 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 30 q5 ∷
   re 24 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "乀") ∷
   rw 26 q2 ∷
   rw⁻ 27 q3 ∷
   rw 28 q4 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 31 q5 ∷
   re 25 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "乀") ∷
   rw 27 q2 ∷
   rw⁻ 28 q3 ∷
   rw 29 q4 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q5 ∷
   re 26 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "乀") ∷
   rw 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw 30 q4 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 33 q5 ∷
   re 27 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 29 3 (ℓ "乀") ∷
   rw 29 q2 ∷
   rw⁻ 30 q3 ∷
   rw 31 q4 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 34 q5 ∷
   re 28 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "乀") ∷
   rw 30 q2 ∷
   rw⁻ 31 q3 ∷
   rw 32 q4 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q5 ∷
   re 29 5 (ℓ "中") ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q5 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q5 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q5 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q5 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q5 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q5 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q5 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q5 ∷
   rw 20 q18 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q5 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q5 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q5 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q5 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q5 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q19 ∷
   rw 8 q20 ∷
   rw 7 q20 ∷
   rw 8 q21 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷ []) Eq.refl
