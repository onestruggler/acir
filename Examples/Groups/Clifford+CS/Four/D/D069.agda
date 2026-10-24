{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D069 (W : Ws) where

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
  q2 = wE 7 W
  q3 : Eqn
  q3 = wE 140 W
  q4 : Eqn
  q4 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 570 W
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q11 : Eqn
  q11 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 21 W
  q15 : Eqn
  q15 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q16 : Eqn
  q16 = wE 51 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 525 W
  q20 : Eqn
  q20 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q21 : Eqn
  q21 = wE 527 W
  q22 : Eqn
  q22 = wE 526 W
  q23 : Eqn
  q23 = wE 571 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [CSd12]: 561 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd12 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丷") ⟫ʷ ≈ ⟪ (ℓ "丷中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd12 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丷") (ℓ "丷中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q1 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q2 ∷
   rw 26 q2 ∷
   rw 25 q2 ∷
   rw⁻ 24 q4 ∷
   rw 23 q2 ∷
   rw 22 q2 ∷
   rw 21 q2 ∷
   rw 20 q2 ∷
   rw 19 q2 ∷
   rw 18 q2 ∷
   rw 17 q2 ∷
   rw 16 q2 ∷
   rw 15 q2 ∷
   rw⁻ 14 q5 ∷
   rw 13 q3 ∷
   rw 12 q2 ∷
   rw 11 q2 ∷
   rw 10 q2 ∷
   rw 9 q2 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   rw⁻ 6 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q6 ∷
   rw 6 q2 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q2 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q3 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q2 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q2 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q2 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 1 q8 ∷
   rw 2 q8 ∷
   rw 3 q9 ∷
   rw 4 q8 ∷
   rw 5 q8 ∷
   rw 6 q10 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q8 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q8 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q8 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 11 q8 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q6 ∷
   rw 12 q8 ∷
   rw 13 q6 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q6 ∷
   rw 13 q8 ∷
   rw 14 q6 ∷
   re 12 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q6 ∷
   rw 14 q9 ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q11 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q6 ∷
   rw 16 q8 ∷
   rw 17 q6 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q6 ∷
   rw 17 q8 ∷
   rw 18 q6 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q6 ∷
   rw 18 q8 ∷
   rw 19 q6 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q6 ∷
   rw 19 q8 ∷
   rw 20 q6 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q6 ∷
   rw 20 q8 ∷
   rw 21 q6 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q6 ∷
   rw 21 q8 ∷
   rw 22 q6 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q6 ∷
   rw 22 q8 ∷
   rw 23 q6 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q6 ∷
   rw 23 q8 ∷
   rw 24 q6 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q6 ∷
   rw 24 q8 ∷
   rw 25 q6 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q10 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q6 ∷
   rw 26 q8 ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q6 ∷
   rw 27 q8 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q6 ∷
   rw 28 q8 ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q6 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q6 ∷
   rw 30 q8 ∷
   rw 31 q6 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q6 ∷
   rw 31 q8 ∷
   rw 32 q6 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q12 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q13 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q14 ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q17 ∷
   re 31 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q13 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q14 ∷
   rw 31 q15 ∷
   rw 30 q16 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q17 ∷
   re 30 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q13 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q14 ∷
   rw 30 q18 ∷
   rw 29 q16 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q17 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q13 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q17 ∷
   re 28 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q13 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q14 ∷
   rw 28 q15 ∷
   rw 27 q16 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q17 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q13 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q14 ∷
   rw 27 q15 ∷
   rw 26 q16 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q17 ∷
   re 26 5 (ℓ "中") ∷
   rw 24 q19 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q13 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q14 ∷
   rw 25 q15 ∷
   rw 24 q16 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q17 ∷
   re 24 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q13 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q14 ∷
   rw 24 q15 ∷
   rw 23 q16 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q17 ∷
   re 23 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q13 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q14 ∷
   rw 23 q15 ∷
   rw 22 q16 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q17 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q13 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q14 ∷
   rw 22 q15 ∷
   rw 21 q16 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q17 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q13 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q14 ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q17 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q13 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   rw 19 q16 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q17 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q13 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q14 ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q17 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q13 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q14 ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q17 ∷
   re 17 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q13 ∷
   re 19 3 (ℓ "举") ∷
   rw 18 q14 ∷
   rw 17 q15 ∷
   rw 16 q16 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q17 ∷
   re 16 5 (ℓ "中") ∷
   rw⁻ 14 q20 ∷
   re 13 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q13 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q14 ∷
   rw 15 q18 ∷
   rw 14 q16 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q17 ∷
   re 14 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q13 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q14 ∷
   rw 14 q15 ∷
   rw 13 q16 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q17 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q13 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q14 ∷
   rw 13 q15 ∷
   rw 12 q16 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q17 ∷
   re 12 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q13 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q14 ∷
   rw 12 q15 ∷
   rw 11 q16 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q17 ∷
   re 11 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q13 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q14 ∷
   rw 11 q15 ∷
   rw 10 q16 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q17 ∷
   re 10 5 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q13 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q14 ∷
   rw 10 q15 ∷
   rw 9 q16 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q17 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q13 ∷
   re 11 3 (ℓ "举") ∷
   rw 10 q14 ∷
   rw 9 q15 ∷
   rw 8 q16 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q17 ∷
   re 8 5 (ℓ "中") ∷
   rw 6 q19 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 32 q1 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q6 ∷
   rw 32 q2 ∷
   rw⁻ 31 q6 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q6 ∷
   rw 31 q2 ∷
   rw⁻ 30 q6 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw⁻ 31 q6 ∷
   rw 30 q3 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (ℓ "乔") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q6 ∷
   rw 29 q2 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q6 ∷
   rw 28 q2 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q6 ∷
   rw 27 q2 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (ℓ "丽") ∷
   rw⁻ 25 q10 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q6 ∷
   rw 25 q2 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q6 ∷
   rw 24 q2 ∷
   rw⁻ 23 q6 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q6 ∷
   rw 23 q2 ∷
   rw⁻ 22 q6 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q6 ∷
   rw 22 q2 ∷
   rw⁻ 21 q6 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q6 ∷
   rw 21 q2 ∷
   rw⁻ 20 q6 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q6 ∷
   rw 20 q2 ∷
   rw⁻ 19 q6 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q6 ∷
   rw 19 q2 ∷
   rw⁻ 18 q6 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q6 ∷
   rw 18 q2 ∷
   rw⁻ 17 q6 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q6 ∷
   rw 17 q2 ∷
   rw⁻ 16 q6 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q11 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q6 ∷
   rw 15 q3 ∷
   rw⁻ 14 q6 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q6 ∷
   rw 14 q2 ∷
   rw⁻ 13 q6 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q6 ∷
   rw 13 q2 ∷
   rw⁻ 12 q6 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q6 ∷
   rw 12 q2 ∷
   rw⁻ 11 q6 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q6 ∷
   rw 11 q2 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q6 ∷
   rw 10 q2 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q2 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 7 q10 ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   rw 1 q2 ∷
   rw 2 q23 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q6 ∷
   rw 2 q8 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q6 ∷
   rw 3 q8 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw 4 q8 ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q6 ∷
   rw 5 q9 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "乑") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q8 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 7 q8 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q4 ∷
   rw 8 q8 ∷
   rw 9 q8 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q9 ∷
   rw 15 q5 ∷
   rw 16 q8 ∷
   rw 17 q8 ∷
   rw 18 q8 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   rw 21 q8 ∷
   rw 22 q8 ∷
   rw 23 q8 ∷
   rw 24 q8 ∷
   rw 25 q4 ∷
   rw 26 q8 ∷
   rw 27 q8 ∷
   rw 28 q8 ∷
   rw 29 q9 ∷
   rw 30 q8 ∷
   rw 31 q8 ∷
   rw 32 q12 ∷ []) Eq.refl
