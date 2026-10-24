{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D443 (W : Ws) where

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
  q2 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 36 W
  q5 : Eqn
  q5 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q6 : Eqn
  q6 = wE 37 W
  q7 : Eqn
  q7 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
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
  q14 = wE 1181 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 464 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q21 : Eqn
  q21 = wE 665 W
  q22 : Eqn
  q22 = wE 151 W
  q23 : Eqn
  q23 = wE 157 W
  q24 : Eqn
  q24 = wE 158 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] part1: 500 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part1 : ⟪ (ℓ "丠丠临丠临临乀丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乏丼临丼乀乏业乑业中中中乑业中中中中中中丧丧丧乄丧丧乀中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧乏乏丼丠乌丼乏乏乄丧丧中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part1 = derive (ℓ "丠丠临丠临临乀丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乏丼临丼乀乏业乑业中中中乑业中中中中中中丧丧丧乄丧丧乀中中乑中乑乑") (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧乏乏丼丠乌丼乏乏乄丧丧中中乑中乑乑")
  (re 35 1 (ℓ "乏丹乏") ∷
   rw 37 q1 ∷
   re 31 5 (ℓ "乑") ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q3 ∷
   re 34 3 (ℓ "乀") ∷
   rw 34 q4 ∷
   rw⁻ 35 q5 ∷
   rw 36 q6 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q1 ∷
   re 33 5 (ℓ "乑") ∷
   rw 34 q2 ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q3 ∷
   re 36 3 (ℓ "乀") ∷
   rw 36 q4 ∷
   rw⁻ 37 q7 ∷
   rw 38 q6 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 41 q1 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q3 ∷
   re 37 3 (ℓ "乀") ∷
   rw 37 q4 ∷
   rw⁻ 38 q7 ∷
   rw 39 q6 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 42 q1 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q3 ∷
   re 38 3 (ℓ "乀") ∷
   rw 38 q4 ∷
   rw⁻ 39 q7 ∷
   rw 40 q6 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 43 q1 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼临丼乏") ∷
   rw 38 q3 ∷
   re 39 3 (ℓ "乀") ∷
   rw 39 q4 ∷
   rw⁻ 40 q5 ∷
   rw 41 q6 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 44 q1 ∷
   re 38 5 (ℓ "乑") ∷
   rw 39 q2 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q3 ∷
   re 41 3 (ℓ "乀") ∷
   rw 41 q4 ∷
   rw⁻ 42 q7 ∷
   rw 43 q6 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 46 q1 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q3 ∷
   re 42 3 (ℓ "乀") ∷
   rw 42 q4 ∷
   rw⁻ 43 q7 ∷
   rw 44 q6 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 47 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q3 ∷
   re 43 3 (ℓ "乀") ∷
   rw 43 q4 ∷
   rw⁻ 44 q7 ∷
   rw 45 q6 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 48 q1 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q3 ∷
   re 44 3 (ℓ "乀") ∷
   rw 44 q4 ∷
   rw⁻ 45 q7 ∷
   rw 46 q6 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 49 q1 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q3 ∷
   re 45 3 (ℓ "乀") ∷
   rw 45 q4 ∷
   rw⁻ 46 q7 ∷
   rw 47 q6 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 50 q1 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q3 ∷
   re 46 3 (ℓ "乀") ∷
   rw 46 q4 ∷
   rw⁻ 47 q7 ∷
   rw 48 q6 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 51 q1 ∷
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
   rw⁻ 39 q11 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw⁻ 40 q9 ∷
   rw 39 q12 ∷
   rw⁻ 38 q9 ∷
   re 39 3 (ℓ "乔") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q9 ∷
   rw 38 q10 ∷
   rw⁻ 37 q9 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q9 ∷
   rw 37 q10 ∷
   rw⁻ 36 q9 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q9 ∷
   rw 36 q10 ∷
   rw⁻ 35 q9 ∷
   re 36 3 (ℓ "丽") ∷
   rw⁻ 34 q11 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q9 ∷
   rw 34 q12 ∷
   rw⁻ 33 q9 ∷
   re 34 3 (ℓ "乔") ∷
   rw⁻ 32 q11 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw⁻ 33 q9 ∷
   rw 32 q12 ∷
   rw⁻ 31 q9 ∷
   re 32 3 (ℓ "乔") ∷
   rw 30 q10 ∷
   rw 29 q10 ∷
   rw 28 q10 ∷
   rw 27 q10 ∷
   rw 26 q10 ∷
   rw 25 q10 ∷
   rw 24 q10 ∷
   rw 23 q10 ∷
   rw 22 q10 ∷
   rw⁻ 21 q13 ∷
   rw 20 q12 ∷
   rw 19 q10 ∷
   rw 18 q10 ∷
   rw 17 q10 ∷
   rw 16 q10 ∷
   rw 15 q10 ∷
   rw 14 q10 ∷
   rw 15 q14 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q9 ∷
   rw 15 q15 ∷
   rw 16 q9 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q11 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q9 ∷
   rw 17 q15 ∷
   rw 18 q9 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q11 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q9 ∷
   rw 19 q16 ∷
   rw 20 q9 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q9 ∷
   rw 20 q16 ∷
   rw 21 q9 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q9 ∷
   rw 21 q16 ∷
   rw 22 q9 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q9 ∷
   rw 22 q15 ∷
   rw 23 q9 ∷
   re 21 3 (ℓ "乑") ∷
   rw 22 q11 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q9 ∷
   rw 24 q16 ∷
   rw 25 q9 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q9 ∷
   rw 25 q16 ∷
   rw 26 q9 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q9 ∷
   rw 26 q16 ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q9 ∷
   rw 27 q16 ∷
   rw 28 q9 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q9 ∷
   rw 28 q16 ∷
   rw 29 q9 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q9 ∷
   rw 29 q16 ∷
   rw 30 q9 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q16 ∷
   rw 30 q16 ∷
   rw 31 q16 ∷
   rw 32 q16 ∷
   rw 33 q16 ∷
   rw 34 q16 ∷
   rw 35 q15 ∷
   rw 36 q13 ∷
   rw 37 q16 ∷
   rw 38 q16 ∷
   rw 39 q16 ∷
   rw 40 q16 ∷
   rw 41 q16 ∷
   rw 42 q16 ∷
   rw 43 q16 ∷
   rw 44 q16 ∷
   rw 45 q16 ∷
   rw 46 q17 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 13 q3 ∷
   re 14 3 (ℓ "乀") ∷
   rw 14 q4 ∷
   rw⁻ 15 q5 ∷
   rw 16 q6 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 19 q1 ∷
   re 13 5 (ℓ "乑") ∷
   rw 14 q2 ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q3 ∷
   re 16 3 (ℓ "乀") ∷
   rw 16 q4 ∷
   rw⁻ 17 q5 ∷
   rw 18 q6 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 21 q1 ∷
   re 15 5 (ℓ "乑") ∷
   rw 16 q2 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q3 ∷
   re 18 3 (ℓ "乀") ∷
   rw 18 q4 ∷
   rw⁻ 19 q7 ∷
   rw 20 q6 ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 23 q1 ∷
   re 17 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q3 ∷
   re 19 3 (ℓ "乀") ∷
   rw 19 q4 ∷
   rw⁻ 20 q7 ∷
   rw 21 q6 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q1 ∷
   re 18 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q3 ∷
   re 20 3 (ℓ "乀") ∷
   rw 20 q4 ∷
   rw⁻ 21 q7 ∷
   rw 22 q6 ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 25 q1 ∷
   re 19 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q3 ∷
   re 21 3 (ℓ "乀") ∷
   rw 21 q4 ∷
   rw⁻ 22 q5 ∷
   rw 23 q6 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q1 ∷
   re 20 5 (ℓ "乑") ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q3 ∷
   re 23 3 (ℓ "乀") ∷
   rw 23 q4 ∷
   rw⁻ 24 q7 ∷
   rw 25 q6 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 28 q1 ∷
   re 22 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q3 ∷
   re 24 3 (ℓ "乀") ∷
   rw 24 q4 ∷
   rw⁻ 25 q7 ∷
   rw 26 q6 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 29 q1 ∷
   re 23 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q3 ∷
   re 25 3 (ℓ "乀") ∷
   rw 25 q4 ∷
   rw⁻ 26 q7 ∷
   rw 27 q6 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 30 q1 ∷
   re 24 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q3 ∷
   re 26 3 (ℓ "乀") ∷
   rw 26 q4 ∷
   rw⁻ 27 q7 ∷
   rw 28 q6 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 31 q1 ∷
   re 25 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q3 ∷
   re 27 3 (ℓ "乀") ∷
   rw 27 q4 ∷
   rw⁻ 28 q7 ∷
   rw 29 q6 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q1 ∷
   re 26 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q3 ∷
   re 28 3 (ℓ "乀") ∷
   rw 28 q4 ∷
   rw⁻ 29 q7 ∷
   rw 30 q6 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 33 q1 ∷
   re 27 5 (ℓ "中") ∷
   rw 28 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q1 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q1 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q1 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q1 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q1 ∷
   rw 21 q18 ∷
   re 20 1 (ℓ "乏乄乏") ∷
   rw 22 q1 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q1 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q1 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q1 ∷
   rw 16 q18 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q1 ∷
   rw 14 q18 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q1 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q19 ∷
   rw 8 q19 ∷
   rw 7 q19 ∷
   rw 8 q21 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q22 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q22 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q22 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw⁻ 25 q20 ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw 28 q1 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 52 q3 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q3 ∷
   re 57 3 (ℓ "乀") ∷
   rw 56 q23 ∷
   rw 55 q7 ∷
   rw 54 q24 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 53 q1 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q1 ∷
   re 52 3 (ℓ "乀") ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 51 q3 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q3 ∷
   re 56 3 (ℓ "乀") ∷
   rw 55 q23 ∷
   rw 54 q7 ∷
   rw 53 q24 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 52 q1 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q1 ∷
   re 51 3 (ℓ "乀") ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 50 q3 ∷
   re 51 3 (ℓ "乑") ∷
   re 51 1 (ℓ "乏丼临丼乏") ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "乀") ∷
   rw 54 q23 ∷
   rw 53 q5 ∷
   rw 52 q24 ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 51 q1 ∷
   re 52 5 (ℓ "乑") ∷
   re 52 1 (ℓ "乏乄乏") ∷
   rw 54 q1 ∷
   re 50 3 (ℓ "乀") ∷
   re 50 1 (ℓ "乏丹乏") ∷
   rw 49 q3 ∷
   re 50 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q3 ∷
   re 54 3 (ℓ "乀") ∷
   rw 53 q23 ∷ []) Eq.refl
