{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D101 (W : Ws) where

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
  q2 = wE 113 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = wE 114 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 640 W
  q7 : Eqn
  q7 = wE 641 W
  q8 : Eqn
  q8 = wE 642 W
  q9 : Eqn
  q9 = wE 643 W
  q10 : Eqn
  q10 = wE 5 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q15 : Eqn
  q15 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q17 : Eqn
  q17 = wE 637 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [CX31] part2: 500 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CX31-part2 : ⟪ (ℓ "乑业乑业中中中乑业中中中中中中乖乏乏丧乏乆乏丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "乓乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中並丽丽丽並") ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CX31-part2 = derive (ℓ "乑业乑业中中中乑业中中中中中中乖乏乏丧乏乆乏丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "乓乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中並丽丽丽並")
  (re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q5 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q5 ∷
   re 16 3 (ℓ "乓") ∷
   rw 15 q6 ∷
   rw 16 q1 ∷
   re 15 1 (ℓ "乏乆乏") ∷
   rw 17 q5 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q5 ∷
   rw 15 q7 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乓") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q5 ∷
   rw 15 q1 ∷
   re 14 1 (ℓ "乏乆乏") ∷
   rw 16 q5 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   rw 14 q7 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乓") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q5 ∷
   rw 14 q1 ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 15 q5 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   rw 13 q7 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乓") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q5 ∷
   rw 13 q1 ∷
   re 12 1 (ℓ "乏乆乏") ∷
   rw 14 q5 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   rw 12 q7 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "乓") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q5 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏乆乏") ∷
   rw 13 q5 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw 11 q7 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乓") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q5 ∷
   rw 11 q1 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 12 q5 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 10 q7 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q5 ∷
   rw 8 q8 ∷
   rw 9 q1 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 10 q5 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q5 ∷
   rw 8 q9 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乓") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q5 ∷
   rw 8 q1 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q5 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 7 q7 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乓") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q5 ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q5 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 6 q7 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乓") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q5 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 5 q7 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乓") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q5 ∷
   rw 3 q8 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏乆乏") ∷
   rw 5 q5 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q5 ∷
   rw 3 q9 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乓") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乑") ∷
   rw 4 q5 ∷
   rw 1 q8 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏乆乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q5 ∷
   rw 1 q9 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "乓") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q5 ∷
   rw 75 q10 ∷
   rw 74 q11 ∷
   rw 73 q11 ∷
   rw 72 q11 ∷
   rw 71 q11 ∷
   rw 70 q11 ∷
   rw 69 q11 ∷
   rw⁻ 68 q12 ∷
   rw 67 q13 ∷
   rw 66 q11 ∷
   rw 65 q11 ∷
   rw 64 q11 ∷
   rw⁻ 63 q12 ∷
   rw 62 q13 ∷
   rw⁻ 61 q12 ∷
   rw 60 q13 ∷
   rw⁻ 59 q14 ∷
   rw⁻ 58 q12 ∷
   rw 57 q13 ∷
   rw⁻ 56 q12 ∷
   rw⁻ 55 q12 ∷
   rw⁻ 54 q12 ∷
   rw⁻ 53 q12 ∷
   rw 52 q13 ∷
   rw⁻ 51 q12 ∷
   rw⁻ 50 q12 ∷
   rw⁻ 49 q12 ∷
   rw 48 q11 ∷
   rw 47 q11 ∷
   rw 46 q11 ∷
   rw 45 q11 ∷
   rw 44 q11 ∷
   rw 43 q11 ∷
   rw 42 q11 ∷
   rw 41 q11 ∷
   rw 40 q11 ∷
   rw⁻ 39 q12 ∷
   rw 38 q13 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 36 q12 ∷
   rw⁻ 35 q12 ∷
   rw 34 q11 ∷
   rw 33 q11 ∷
   rw 32 q11 ∷
   rw 31 q11 ∷
   rw 30 q11 ∷
   rw 29 q11 ∷
   rw 28 q11 ∷
   rw 27 q11 ∷
   rw 26 q11 ∷
   rw 25 q11 ∷
   rw 24 q11 ∷
   rw 23 q11 ∷
   rw 22 q11 ∷
   rw 21 q11 ∷
   rw 20 q11 ∷
   rw 19 q11 ∷
   rw 18 q11 ∷
   rw 17 q11 ∷
   rw⁻ 16 q14 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q15 ∷
   rw 16 q11 ∷
   rw⁻ 15 q15 ∷
   re 16 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q15 ∷
   rw 15 q11 ∷
   rw⁻ 14 q15 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q15 ∷
   rw 14 q11 ∷
   rw⁻ 13 q15 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q15 ∷
   rw 13 q11 ∷
   rw⁻ 12 q15 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q15 ∷
   rw 12 q11 ∷
   rw⁻ 11 q15 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q15 ∷
   rw 11 q11 ∷
   rw⁻ 10 q15 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 9 q16 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw⁻ 10 q15 ∷
   rw 9 q13 ∷
   rw⁻ 8 q15 ∷
   re 9 3 (ℓ "乔") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q15 ∷
   rw 8 q11 ∷
   rw⁻ 7 q15 ∷
   re 8 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q15 ∷
   rw 7 q11 ∷
   rw⁻ 6 q15 ∷
   re 7 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q15 ∷
   rw 6 q11 ∷
   rw⁻ 5 q15 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 4 q16 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q15 ∷
   rw 4 q13 ∷
   rw⁻ 3 q15 ∷
   re 4 3 (ℓ "乔") ∷
   rw⁻ 2 q16 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw⁻ 3 q15 ∷
   rw 2 q13 ∷
   rw⁻ 1 q15 ∷
   re 2 3 (ℓ "乔") ∷
   rw 2 q17 ∷
   rw 1 q18 ∷
   rw 2 q12 ∷
   rw 3 q18 ∷
   rw 4 q12 ∷
   rw 5 q19 ∷
   rw 6 q19 ∷
   rw 7 q19 ∷
   rw 8 q18 ∷
   rw 9 q12 ∷
   rw 10 q19 ∷
   rw 11 q19 ∷
   rw 12 q19 ∷
   rw 13 q19 ∷
   rw 14 q19 ∷
   rw 15 q19 ∷
   rw 16 q20 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q15 ∷
   rw 18 q19 ∷
   rw 19 q15 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q15 ∷
   rw 19 q19 ∷
   rw 20 q15 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q15 ∷
   rw 20 q19 ∷
   rw 21 q15 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q15 ∷
   rw 21 q19 ∷
   rw 22 q15 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q15 ∷
   rw 22 q19 ∷
   rw 23 q15 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q15 ∷
   rw 23 q19 ∷
   rw 24 q15 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q15 ∷
   rw 24 q19 ∷
   rw 25 q15 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q15 ∷
   rw 25 q19 ∷
   rw 26 q15 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q15 ∷
   rw 26 q19 ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q15 ∷
   rw 27 q19 ∷
   rw 28 q15 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q15 ∷
   rw 28 q19 ∷
   rw 29 q15 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q15 ∷
   rw 29 q19 ∷
   rw 30 q15 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q15 ∷
   rw 30 q19 ∷
   rw 31 q15 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q15 ∷
   rw 31 q19 ∷
   rw 32 q15 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q15 ∷
   rw 32 q19 ∷
   rw 33 q15 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q15 ∷
   rw 33 q19 ∷
   rw 34 q15 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q15 ∷
   rw 34 q19 ∷
   rw 35 q15 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q15 ∷
   rw 35 q19 ∷
   rw 36 q15 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q16 ∷
   rw 36 q16 ∷
   rw 37 q16 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q15 ∷
   rw 39 q18 ∷
   rw 40 q15 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q16 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q15 ∷
   rw 41 q19 ∷
   rw 42 q15 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q15 ∷
   rw 42 q19 ∷
   rw 43 q15 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q15 ∷
   rw 43 q19 ∷
   rw 44 q15 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q15 ∷
   rw 44 q19 ∷
   rw 45 q15 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q15 ∷
   rw 45 q19 ∷
   rw 46 q15 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q15 ∷
   rw 46 q19 ∷
   rw 47 q15 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q15 ∷
   rw 47 q19 ∷
   rw 48 q15 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q15 ∷
   rw 48 q19 ∷
   rw 49 q15 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q15 ∷
   rw 49 q19 ∷
   rw 50 q15 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q16 ∷
   rw 50 q16 ∷
   rw 51 q16 ∷
   re 53 1 (ℓ "乏乇乏") ∷
   rw 52 q15 ∷
   rw 53 q18 ∷
   rw 54 q15 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q16 ∷
   rw 54 q16 ∷
   rw 55 q16 ∷
   rw 56 q16 ∷
   re 58 1 (ℓ "乏乇乏") ∷
   rw 57 q15 ∷
   rw 58 q18 ∷
   rw 59 q15 ∷
   re 57 3 (ℓ "乑") ∷
   rw 58 q16 ∷
   rw 59 q20 ∷
   re 61 1 (ℓ "乏乇乏") ∷
   rw 60 q15 ∷
   rw 61 q18 ∷
   rw 62 q15 ∷
   re 60 3 (ℓ "乑") ∷
   rw 61 q16 ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 62 q15 ∷
   rw 63 q18 ∷
   rw 64 q15 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q16 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q15 ∷
   rw 65 q19 ∷
   rw 66 q15 ∷
   re 64 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q15 ∷
   rw 66 q19 ∷
   rw 67 q15 ∷
   re 65 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q15 ∷
   rw 67 q19 ∷
   rw 68 q15 ∷
   re 66 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q15 ∷
   rw 68 q18 ∷
   rw 69 q15 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q16 ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q15 ∷
   rw 70 q19 ∷
   rw 71 q15 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q15 ∷
   rw 71 q19 ∷
   rw 72 q15 ∷
   re 70 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q15 ∷
   rw 72 q19 ∷
   rw 73 q15 ∷
   re 71 3 (ℓ "中") ∷ []) Eq.refl
