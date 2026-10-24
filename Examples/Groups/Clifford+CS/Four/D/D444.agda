{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D444 (W : Ws) where

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
  q1 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q2 : Eqn
  q2 = wE 158 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 157 W
  q6 : Eqn
  q6 = wE 624 W
  q7 : Eqn
  q7 = wE 625 W
  q8 : Eqn
  q8 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q9 : Eqn
  q9 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = wE 1126 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 140 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 1182 W
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
  q23 = wE 1183 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] part2: 500 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part2 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧乏乏丼丠乌丼乏乏乄丧丧中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀丠丠丠临丠丠丹中中乑中乏並乇乏乔丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶並丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part2 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧乏乏丼丠乌丼乏乏乄丧丧中中乑中乑乑") (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀丠丠丠临丠丠丹中中乑中乏並乇乏乔丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶並丹丧丧丧乄丧丧")
  (rw 52 q1 ∷
   rw 51 q2 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 50 q3 ∷
   re 51 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q3 ∷
   re 49 3 (ℓ "乀") ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 48 q4 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q4 ∷
   re 53 3 (ℓ "乀") ∷
   rw 52 q5 ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   re 50 1 (ℓ "乏丹乏") ∷
   rw 49 q3 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q3 ∷
   re 48 3 (ℓ "乀") ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 47 q4 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q4 ∷
   re 52 3 (ℓ "乀") ∷
   rw 51 q5 ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 48 q3 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q3 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q6 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q4 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q4 ∷
   re 50 3 (ℓ "乀") ∷
   rw 49 q5 ∷
   rw 48 q1 ∷
   rw 47 q2 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 46 q3 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q3 ∷
   re 45 3 (ℓ "乀") ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q4 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q4 ∷
   re 49 3 (ℓ "乀") ∷
   rw 48 q5 ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q3 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q3 ∷
   re 44 3 (ℓ "乀") ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q4 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q4 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q5 ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q3 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   re 43 3 (ℓ "乀") ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q4 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q4 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q5 ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q3 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q3 ∷
   re 42 3 (ℓ "乀") ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q4 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q4 ∷
   re 46 3 (ℓ "乀") ∷
   rw 45 q5 ∷
   rw 44 q1 ∷
   rw 43 q2 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q3 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q3 ∷
   re 41 3 (ℓ "乀") ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q4 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q4 ∷
   re 45 3 (ℓ "乀") ∷
   rw 44 q5 ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q3 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 40 3 (ℓ "乀") ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q4 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q4 ∷
   re 44 3 (ℓ "乀") ∷
   rw 43 q5 ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q3 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q3 ∷
   re 39 3 (ℓ "乀") ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q4 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q4 ∷
   re 43 3 (ℓ "乀") ∷
   rw 42 q5 ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q3 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 38 3 (ℓ "乀") ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q4 ∷
   re 38 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q4 ∷
   re 42 3 (ℓ "乀") ∷
   rw 41 q5 ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q3 ∷
   re 39 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q7 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q4 ∷
   re 36 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q4 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q5 ∷
   rw 38 q8 ∷
   rw 37 q2 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q3 ∷
   re 37 5 (ℓ "乑") ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q3 ∷
   re 35 3 (ℓ "乀") ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q4 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q4 ∷
   re 39 3 (ℓ "乀") ∷
   rw 38 q5 ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q3 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q3 ∷
   re 34 3 (ℓ "乀") ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q4 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q4 ∷
   re 38 3 (ℓ "乀") ∷
   rw 37 q5 ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q3 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q3 ∷
   re 33 3 (ℓ "乀") ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q4 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q4 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q5 ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q3 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q3 ∷
   re 32 3 (ℓ "乀") ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q4 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q4 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q5 ∷
   rw 34 q1 ∷
   rw 33 q2 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q3 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q3 ∷
   re 31 3 (ℓ "乀") ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q4 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q4 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q5 ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q3 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q3 ∷
   re 30 3 (ℓ "乀") ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q4 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q5 ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q3 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q3 ∷
   re 29 3 (ℓ "乀") ∷
   rw 28 q6 ∷
   rw 29 q4 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 30 q3 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 22 q9 ∷
   rw 23 q11 ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "乀") ∷
   rw⁻ 23 q9 ∷
   rw⁻ 24 q9 ∷
   rw⁻ 25 q9 ∷
   rw⁻ 26 q10 ∷
   rw⁻ 27 q9 ∷
   rw⁻ 28 q9 ∷
   rw 29 q3 ∷
   rw 60 q12 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw⁻ 61 q13 ∷
   rw 60 q14 ∷
   rw⁻ 59 q13 ∷
   re 60 3 (ℓ "乔") ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw⁻ 60 q13 ∷
   rw 59 q14 ∷
   rw⁻ 58 q13 ∷
   re 59 3 (ℓ "乔") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q13 ∷
   rw 58 q15 ∷
   rw⁻ 57 q13 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw⁻ 58 q13 ∷
   rw 57 q14 ∷
   rw⁻ 56 q13 ∷
   re 57 3 (ℓ "乔") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q13 ∷
   rw 56 q15 ∷
   rw⁻ 55 q13 ∷
   re 56 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q13 ∷
   rw 55 q15 ∷
   rw⁻ 54 q13 ∷
   re 55 3 (ℓ "丽") ∷
   rw 53 q15 ∷
   rw 52 q15 ∷
   rw 51 q14 ∷
   rw 50 q15 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 49 q16 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q13 ∷
   rw 49 q17 ∷
   rw 50 q13 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q13 ∷
   rw 50 q17 ∷
   rw 51 q13 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏乇乏") ∷
   rw 50 q13 ∷
   rw 51 q18 ∷
   rw 52 q13 ∷
   re 50 3 (ℓ "乑") ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q13 ∷
   rw 52 q17 ∷
   rw 53 q13 ∷
   re 51 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏乇乏") ∷
   rw 52 q13 ∷
   rw 53 q18 ∷
   rw 54 q13 ∷
   re 52 3 (ℓ "乑") ∷
   re 54 1 (ℓ "乏乇乏") ∷
   rw 53 q13 ∷
   rw 54 q18 ∷
   rw 55 q13 ∷
   re 53 3 (ℓ "乑") ∷
   rw 54 q17 ∷
   rw 55 q17 ∷
   rw 56 q17 ∷
   rw 57 q18 ∷
   rw 58 q17 ∷
   rw 59 q17 ∷
   rw 60 q19 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q4 ∷
   re 48 3 (ℓ "乀") ∷
   rw 48 q20 ∷
   rw⁻ 49 q1 ∷
   rw 50 q21 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 53 q3 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q4 ∷
   re 49 3 (ℓ "乀") ∷
   rw 49 q20 ∷
   rw⁻ 50 q1 ∷
   rw 51 q21 ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 54 q3 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼临丼乏") ∷
   rw 49 q4 ∷
   re 50 3 (ℓ "乀") ∷
   rw 50 q20 ∷
   rw⁻ 51 q8 ∷
   rw 52 q21 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 55 q3 ∷
   re 49 5 (ℓ "乑") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q4 ∷
   re 51 3 (ℓ "乀") ∷
   rw 51 q20 ∷
   rw⁻ 52 q1 ∷
   rw 53 q21 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 56 q3 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼临丼乏") ∷
   rw 51 q4 ∷
   re 52 3 (ℓ "乀") ∷
   rw 52 q20 ∷
   rw⁻ 53 q8 ∷
   rw 54 q21 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 57 q3 ∷
   re 51 5 (ℓ "乑") ∷
   re 53 1 (ℓ "乏丼临丼乏") ∷
   rw 52 q4 ∷
   re 53 3 (ℓ "乀") ∷
   rw 53 q20 ∷
   rw⁻ 54 q8 ∷
   rw 55 q21 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 58 q3 ∷
   re 52 5 (ℓ "乑") ∷
   rw 53 q12 ∷
   re 52 1 (ℓ "乏乄乏") ∷
   rw⁻ 54 q13 ∷
   rw 53 q14 ∷
   rw⁻ 52 q13 ∷
   re 53 3 (ℓ "乔") ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw⁻ 53 q13 ∷
   rw 52 q14 ∷
   rw⁻ 51 q13 ∷
   re 52 3 (ℓ "乔") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q13 ∷
   rw 51 q15 ∷
   rw⁻ 50 q13 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw⁻ 51 q13 ∷
   rw 50 q14 ∷
   rw⁻ 49 q13 ∷
   re 50 3 (ℓ "乔") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q13 ∷
   rw 49 q15 ∷
   rw⁻ 48 q13 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q13 ∷
   rw 48 q15 ∷
   rw⁻ 47 q13 ∷
   re 48 3 (ℓ "丽") ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 38 q15 ∷
   rw⁻ 37 q22 ∷
   rw 36 q14 ∷
   rw 35 q15 ∷
   rw 34 q15 ∷
   rw 33 q15 ∷
   rw 32 q15 ∷
   rw 31 q15 ∷
   rw 30 q15 ∷
   rw 31 q23 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q13 ∷
   rw 31 q17 ∷
   rw 32 q13 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q13 ∷
   rw 32 q17 ∷
   rw 33 q13 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏乇乏") ∷
   rw 32 q13 ∷
   rw 33 q18 ∷
   rw 34 q13 ∷
   re 32 3 (ℓ "乑") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q13 ∷
   rw 34 q17 ∷
   rw 35 q13 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q13 ∷ []) Eq.refl
