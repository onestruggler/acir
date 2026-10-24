{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D394 (W : Ws) where

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
  q1 = wE 1118 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 157 W
  q4 : Eqn
  q4 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q5 : Eqn
  q5 = wE 158 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q8 : Eqn
  q8 = wE 624 W
  q9 : Eqn
  q9 = wE 625 W
  q10 : Eqn
  q10 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = wE 1115 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = wE 1119 W
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = wE 36 W
  q23 : Eqn
  q23 = wE 37 W
  q24 : Eqn
  q24 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03] part0: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part0 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠临丠乀中中中乑业中中中中中中乀中中乑中") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠乀丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中乑业中中中中中乏丼丠丼乀乏丧丧乄丧乄乄乀中中乑中") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part0 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠临丠乀中中中乑业中中中中中中乀中中乑中") (ℓ "丠丠临丠乀丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中乑业中中中中中乏丼丠丼乀乏丧丧乄丧乄乄乀中中乑中")
  (rw 0 q1 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q2 ∷
   re 33 3 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丼临丼乏") ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q6 ∷
   re 34 5 (ℓ "乑") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q6 ∷
   re 32 3 (ℓ "乀") ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q2 ∷
   re 32 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏丼临丼乏") ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q6 ∷
   re 33 5 (ℓ "乑") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q6 ∷
   re 31 3 (ℓ "乀") ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q2 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q3 ∷
   rw 33 q7 ∷
   rw 32 q5 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q6 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q6 ∷
   re 30 3 (ℓ "乀") ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丼临丼乏") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q6 ∷
   re 31 5 (ℓ "乑") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q6 ∷
   re 29 3 (ℓ "乀") ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乀") ∷
   rw 32 q3 ∷
   rw 31 q7 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "乀") ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q3 ∷
   rw 30 q7 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "乀") ∷
   rw 26 q8 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q3 ∷
   rw 28 q7 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "乀") ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q3 ∷
   rw 27 q7 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "乀") ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乀") ∷
   rw 27 q3 ∷
   rw 26 q7 ∷
   rw 25 q5 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 24 q6 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 23 3 (ℓ "乀") ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "乀") ∷
   rw 26 q3 ∷
   rw 25 q7 ∷
   rw 24 q5 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q6 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   re 22 3 (ℓ "乀") ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "乀") ∷
   rw 25 q3 ∷
   rw 24 q7 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "乀") ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乀") ∷
   rw 24 q3 ∷
   rw 23 q7 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "乀") ∷
   rw 19 q9 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "乑") ∷
   re 19 1 (ℓ "乏丼临丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "乀") ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏丹乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "乑") ∷
   re 20 1 (ℓ "乏乄乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "乀") ∷
   re 18 1 (ℓ "乏丹乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乀") ∷
   rw 21 q3 ∷
   rw 20 q7 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "乀") ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q2 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "乀") ∷
   rw 20 q3 ∷
   rw 19 q7 ∷
   rw 18 q5 ∷
   re 18 1 (ℓ "乏丹乏") ∷
   rw 17 q6 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q6 ∷
   re 16 3 (ℓ "乀") ∷
   re 16 1 (ℓ "乏丹乏") ∷
   rw 15 q2 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "乀") ∷
   rw 19 q3 ∷
   rw 18 q7 ∷
   rw 17 q5 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q6 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q6 ∷
   re 15 3 (ℓ "乀") ∷
   rw 14 q9 ∷
   re 14 1 (ℓ "乏丹乏") ∷
   rw 13 q2 ∷
   re 14 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "乀") ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   rw 15 q5 ∷
   re 15 1 (ℓ "乏丹乏") ∷
   rw 14 q6 ∷
   re 15 5 (ℓ "乑") ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q6 ∷
   re 13 3 (ℓ "乀") ∷
   rw 12 q9 ∷
   re 12 1 (ℓ "乏丹乏") ∷
   rw 11 q2 ∷
   re 12 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丼临丼乏") ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "乀") ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   re 13 1 (ℓ "乏丹乏") ∷
   rw 12 q6 ∷
   re 13 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q6 ∷
   re 11 3 (ℓ "乀") ∷
   rw 10 q8 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 12 q6 ∷
   rw 9 q10 ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   rw 6 q10 ∷
   rw 5 q11 ∷
   rw 4 q11 ∷
   rw 5 q12 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "乀") ∷
   rw⁻ 5 q11 ∷
   rw⁻ 6 q11 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 8 q11 ∷
   rw⁻ 9 q10 ∷
   rw⁻ 10 q10 ∷
   rw 11 q6 ∷
   rw 45 q13 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q14 ∷
   rw 45 q15 ∷
   rw⁻ 44 q14 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q14 ∷
   rw 44 q15 ∷
   rw⁻ 43 q14 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q14 ∷
   rw 43 q15 ∷
   rw⁻ 42 q14 ∷
   re 43 3 (ℓ "丽") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q14 ∷
   rw 42 q15 ∷
   rw⁻ 41 q14 ∷
   re 42 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q14 ∷
   rw 41 q15 ∷
   rw⁻ 40 q14 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q14 ∷
   rw 40 q15 ∷
   rw⁻ 39 q14 ∷
   re 40 3 (ℓ "丽") ∷
   rw⁻ 38 q16 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q14 ∷
   rw 38 q17 ∷
   rw⁻ 37 q14 ∷
   re 38 3 (ℓ "乔") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q14 ∷
   rw 37 q15 ∷
   rw⁻ 36 q14 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q14 ∷
   rw 36 q15 ∷
   rw⁻ 35 q14 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q14 ∷
   rw 35 q15 ∷
   rw⁻ 34 q14 ∷
   re 35 3 (ℓ "丽") ∷
   rw 33 q17 ∷
   rw 32 q17 ∷
   rw 31 q15 ∷
   rw 30 q17 ∷
   rw 29 q15 ∷
   rw 28 q15 ∷
   rw 29 q18 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q14 ∷
   rw 29 q19 ∷
   rw 30 q14 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q14 ∷
   rw 30 q19 ∷
   rw 31 q14 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q14 ∷
   rw 31 q19 ∷
   rw 32 q14 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q14 ∷
   rw 32 q20 ∷
   rw 33 q14 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q16 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q14 ∷
   rw 34 q19 ∷
   rw 35 q14 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q14 ∷
   rw 35 q19 ∷
   rw 36 q14 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q14 ∷
   rw 36 q19 ∷
   rw 37 q14 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q14 ∷
   rw 37 q19 ∷
   rw 38 q14 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q14 ∷
   rw 38 q19 ∷
   rw 39 q14 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q14 ∷
   rw 39 q19 ∷
   rw 40 q14 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q19 ∷
   rw 40 q19 ∷
   rw 41 q20 ∷
   rw 42 q19 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q21 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "乀") ∷
   rw 28 q22 ∷
   rw⁻ 29 q7 ∷
   rw 30 q23 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 33 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "乀") ∷
   rw 29 q22 ∷
   rw⁻ 30 q7 ∷
   rw 31 q23 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 34 q6 ∷
   re 28 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "乀") ∷
   rw 30 q22 ∷
   rw⁻ 31 q7 ∷
   rw 32 q23 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 30 q2 ∷
   re 31 3 (ℓ "乀") ∷
   rw 31 q22 ∷
   rw⁻ 32 q4 ∷
   rw 33 q23 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 36 q6 ∷
   re 30 5 (ℓ "乑") ∷
   rw 31 q24 ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 33 3 (ℓ "乀") ∷
   rw 33 q22 ∷
   rw⁻ 34 q7 ∷
   rw 35 q23 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 38 q6 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q2 ∷
   re 34 3 (ℓ "乀") ∷
   rw 34 q22 ∷
   rw⁻ 35 q7 ∷
   rw 36 q23 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q6 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 35 3 (ℓ "乀") ∷
   rw 35 q22 ∷
   rw⁻ 36 q7 ∷
   rw 37 q23 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q6 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q2 ∷
   re 36 3 (ℓ "乀") ∷
   rw 36 q22 ∷
   rw⁻ 37 q7 ∷
   rw 38 q23 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 41 q6 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q2 ∷
   re 37 3 (ℓ "乀") ∷
   rw 37 q22 ∷
   rw⁻ 38 q7 ∷
   rw 39 q23 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 42 q6 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q2 ∷
   re 38 3 (ℓ "乀") ∷
   rw 38 q22 ∷
   rw⁻ 39 q7 ∷
   rw 40 q23 ∷ []) Eq.refl
