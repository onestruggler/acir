{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D119 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 676 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [CS23]: 207 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS23 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑义") ⟫ʷ ≈ ⟪ (ℓ "义丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS23 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑义") (ℓ "义丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q5 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q5 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q5 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q5 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q5 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q5 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q5 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q5 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q5 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q7 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q4 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q5 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q5 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q5 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q7 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q4 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q7 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q3 ∷
   rw 8 q4 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q6 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q4 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q10 ∷
   rw 7 q6 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q3 ∷
   rw 9 q10 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q7 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q3 ∷
   rw 11 q10 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q7 ∷
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
   rw 16 q7 ∷
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
   rw 23 q6 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q9 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   rw 26 q9 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q3 ∷
   rw 27 q10 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "乑") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   rw 28 q9 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q3 ∷
   rw 29 q10 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   rw 30 q10 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 20 W
  q14 : Eqn
  q14 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q15 : Eqn
  q15 = wE 49 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q18 : Eqn
  q18 = wE 59 W
  q19 : Eqn
  q19 = eqn (ℓ "丶业") (ℓ "业丶") (low₃-comm ((CS ↑)) (S))
  q20 : Eqn
  q20 = wE 523 W
  q21 : Eqn
  q21 = wE 524 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [CS12]: 173 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS12 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丶") ⟫ʷ ≈ ⟪ (ℓ "丶丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS12 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丶") (ℓ "丶丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q12 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q13 ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q16 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q12 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q13 ∷
   rw 29 q14 ∷
   rw 28 q15 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q16 ∷
   re 28 5 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q12 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q13 ∷
   rw 28 q17 ∷
   rw 27 q15 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q16 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼临丼乏") ∷
   rw 31 q12 ∷
   re 29 3 (ℓ "丽") ∷
   rw 28 q13 ∷
   rw 27 q14 ∷
   rw 26 q15 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q16 ∷
   re 26 5 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q12 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q13 ∷
   rw 26 q17 ∷
   rw 25 q15 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q16 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q12 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q13 ∷
   rw 25 q17 ∷
   rw 24 q15 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q16 ∷
   re 24 5 (ℓ "中") ∷
   rw 22 q18 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q12 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q13 ∷
   rw 23 q17 ∷
   rw 22 q15 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q16 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q12 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q13 ∷
   rw 22 q17 ∷
   rw 21 q15 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q16 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q12 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q13 ∷
   rw 21 q17 ∷
   rw 20 q15 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q16 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q12 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q13 ∷
   rw 20 q17 ∷
   rw 19 q15 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q16 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q12 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q13 ∷
   rw 19 q17 ∷
   rw 18 q15 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q16 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q12 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q13 ∷
   rw 18 q17 ∷
   rw 17 q15 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q16 ∷
   re 17 5 (ℓ "中") ∷
   rw⁻ 15 q19 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q12 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q13 ∷
   rw 16 q14 ∷
   rw 15 q15 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q16 ∷
   re 15 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q12 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q13 ∷
   rw 15 q17 ∷
   rw 14 q15 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q16 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q12 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q13 ∷
   rw 14 q17 ∷
   rw 13 q15 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q16 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q12 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q13 ∷
   rw 13 q17 ∷
   rw 12 q15 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q16 ∷
   re 12 5 (ℓ "中") ∷
   rw⁻ 10 q19 ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q12 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q13 ∷
   rw 11 q14 ∷
   rw 10 q15 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q16 ∷
   re 10 5 (ℓ "乑") ∷
   rw⁻ 8 q19 ∷
   re 7 1 (ℓ "乏丼临丼乏") ∷
   rw 13 q12 ∷
   re 11 3 (ℓ "丽") ∷
   rw 10 q13 ∷
   rw 9 q14 ∷
   rw 8 q15 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q16 ∷
   re 8 5 (ℓ "乑") ∷
   rw 6 q18 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷ []) Eq.refl
