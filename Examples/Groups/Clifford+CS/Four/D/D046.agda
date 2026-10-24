{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D046 (W : Ws) where

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
  q2 = wE 140 W
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 513 W
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
  q15 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q16 : Eqn
  q16 = wE 51 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 525 W
  q20 : Eqn
  q20 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q21 : Eqn
  q21 = wE 526 W
  q22 : Eqn
  q22 = wE 527 W
  q23 : Eqn
  q23 = wE 517 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [CSd12]: 487 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丷") ⟫ʷ ≈ ⟪ (ℓ "丷中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丷") (ℓ "丷中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw⁻ 22 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw⁻ 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw⁻ 10 q5 ∷
   rw 9 q2 ∷
   rw⁻ 8 q5 ∷
   rw 7 q2 ∷
   rw⁻ 6 q4 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q6 ∷
   rw 6 q2 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q2 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q3 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q2 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q3 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q3 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 1 q8 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 7 q6 ∷
   rw 8 q9 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q11 ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q11 ∷
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
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q6 ∷
   rw 14 q8 ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q6 ∷
   rw 15 q9 ∷
   rw 16 q6 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q11 ∷
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
   rw 22 q10 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q6 ∷
   rw 24 q8 ∷
   rw 25 q6 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q6 ∷
   rw 25 q8 ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q6 ∷
   rw 26 q9 ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q6 ∷
   rw 27 q8 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q6 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q12 ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q13 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q14 ∷
   rw 30 q15 ∷
   rw 29 q16 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q17 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q13 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q17 ∷
   re 28 5 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q13 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q14 ∷
   rw 28 q18 ∷
   rw 27 q16 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q17 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼临丼乏") ∷
   rw 31 q13 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q14 ∷
   rw 27 q15 ∷
   rw 26 q16 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q17 ∷
   re 26 5 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q13 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q14 ∷
   rw 26 q18 ∷
   rw 25 q16 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q17 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q13 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q14 ∷
   rw 25 q18 ∷
   rw 24 q16 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q17 ∷
   re 24 5 (ℓ "中") ∷
   rw 22 q19 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q13 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q14 ∷
   rw 23 q18 ∷
   rw 22 q16 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q17 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q13 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q14 ∷
   rw 22 q18 ∷
   rw 21 q16 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q17 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q13 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q14 ∷
   rw 21 q18 ∷
   rw 20 q16 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q17 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q13 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q14 ∷
   rw 20 q18 ∷
   rw 19 q16 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q17 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q13 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q14 ∷
   rw 19 q18 ∷
   rw 18 q16 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q17 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q13 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q14 ∷
   rw 18 q18 ∷
   rw 17 q16 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q17 ∷
   re 17 5 (ℓ "中") ∷
   rw⁻ 15 q20 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q13 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q14 ∷
   rw 16 q15 ∷
   rw 15 q16 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q17 ∷
   re 15 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q13 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q14 ∷
   rw 15 q18 ∷
   rw 14 q16 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q17 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q13 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q14 ∷
   rw 14 q18 ∷
   rw 13 q16 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q17 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q13 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q14 ∷
   rw 13 q18 ∷
   rw 12 q16 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q17 ∷
   re 12 5 (ℓ "中") ∷
   rw⁻ 10 q20 ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q13 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q14 ∷
   rw 11 q15 ∷
   rw 10 q16 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q17 ∷
   re 10 5 (ℓ "乑") ∷
   rw⁻ 8 q20 ∷
   re 7 1 (ℓ "乏丼临丼乏") ∷
   rw 13 q13 ∷
   re 11 3 (ℓ "举") ∷
   rw 10 q14 ∷
   rw 9 q15 ∷
   rw 8 q16 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q17 ∷
   re 8 5 (ℓ "乑") ∷
   rw 6 q19 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q22 ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw⁻ 31 q6 ∷
   rw 30 q2 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (ℓ "乔") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q6 ∷
   rw 29 q2 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q6 ∷
   rw 28 q3 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw⁻ 28 q6 ∷
   rw 27 q2 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (ℓ "乔") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q6 ∷
   rw 26 q3 ∷
   rw⁻ 25 q6 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q6 ∷
   rw 25 q3 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (ℓ "丽") ∷
   rw⁻ 23 q10 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q6 ∷
   rw 23 q3 ∷
   rw⁻ 22 q6 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q6 ∷
   rw 22 q3 ∷
   rw⁻ 21 q6 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q6 ∷
   rw 21 q3 ∷
   rw⁻ 20 q6 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q6 ∷
   rw 20 q3 ∷
   rw⁻ 19 q6 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q6 ∷
   rw 19 q3 ∷
   rw⁻ 18 q6 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q6 ∷
   rw 18 q3 ∷
   rw⁻ 17 q6 ∷
   re 18 3 (ℓ "丽") ∷
   rw⁻ 16 q11 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q6 ∷
   rw 16 q2 ∷
   rw⁻ 15 q6 ∷
   re 16 3 (ℓ "乔") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q6 ∷
   rw 15 q3 ∷
   rw⁻ 14 q6 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q6 ∷
   rw 14 q3 ∷
   rw⁻ 13 q6 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q6 ∷
   rw 13 q3 ∷
   rw⁻ 12 q6 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 11 q11 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw⁻ 12 q6 ∷
   rw 11 q2 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (ℓ "乔") ∷
   rw⁻ 9 q11 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q2 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "乔") ∷
   rw⁻ 7 q10 ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
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
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q6 ∷
   rw 4 q9 ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "乑") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 5 q8 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q6 ∷
   rw 6 q9 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q6 ∷
   rw 7 q9 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q4 ∷
   rw 8 q9 ∷
   rw 9 q5 ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q8 ∷
   rw 15 q9 ∷
   rw 16 q5 ∷
   rw 17 q8 ∷
   rw 18 q8 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   rw 21 q8 ∷
   rw 22 q8 ∷
   rw 23 q4 ∷
   rw 24 q8 ∷
   rw 25 q8 ∷
   rw 26 q9 ∷
   rw 27 q8 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q12 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (ℓ "两丞") (ℓ "丞两") (low-comm (CK₀₁) ((X ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "两乗") (ℓ "乗两") (low-comm (CK₀₁) (CK₁₀))
  q26 : Eqn
  q26 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q28 : Eqn
  q28 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q29 : Eqn
  q29 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q30 : Eqn
  q30 = wE 6 W
  q31 : Eqn
  q31 = wE 528 W
  q32 : Eqn
  q32 = wE 39 W
  q33 : Eqn
  q33 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q34 : Eqn
  q34 = eqn (ℓ "丈乗") (ℓ "乗丈") (low₁-comm (S) ((CK₁₀ ↑)))
  q35 : Eqn
  q35 = wE 529 W
  q36 : Eqn
  q36 = wE 530 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01] [X3 CK32 X3]: 107 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK32-X3 : ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乗丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两") ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK32-X3 = derive (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乗丞") (ℓ "丞乗丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两")
  (rw 28 q24 ∷
   rw 29 q25 ∷
   rw 30 q24 ∷
   rw 27 q24 ∷
   rw 28 q25 ∷
   rw 29 q24 ∷
   rw 26 q26 ∷
   rw 27 q27 ∷
   rw 28 q26 ∷
   rw 25 q24 ∷
   rw 26 q25 ∷
   rw 27 q24 ∷
   rw 24 q26 ∷
   rw 25 q27 ∷
   rw 26 q26 ∷
   rw 23 q26 ∷
   rw 24 q27 ∷
   rw 25 q26 ∷
   rw 26 q1 ∷
   rw⁻ 25 q28 ∷
   rw⁻ 24 q29 ∷
   rw⁻ 23 q28 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw⁻ 24 q6 ∷
   rw 23 q30 ∷
   rw⁻ 22 q6 ∷
   re 23 3 (ℓ "乓") ∷
   rw 23 q31 ∷
   rw 22 q28 ∷
   rw 23 q29 ∷
   rw 24 q28 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q6 ∷
   rw 26 q32 ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q12 ∷
   rw 21 q26 ∷
   rw 22 q27 ∷
   rw 23 q26 ∷
   rw 20 q26 ∷
   rw 21 q27 ∷
   rw 22 q26 ∷
   rw 19 q26 ∷
   rw 20 q27 ∷
   rw 21 q26 ∷
   rw 18 q26 ∷
   rw 19 q27 ∷
   rw 20 q26 ∷
   rw 17 q26 ∷
   rw 18 q27 ∷
   rw 19 q26 ∷
   rw 16 q26 ∷
   rw 17 q27 ∷
   rw 18 q26 ∷
   rw 15 q33 ∷
   rw 16 q34 ∷
   rw 17 q33 ∷
   rw 14 q24 ∷
   rw 15 q25 ∷
   rw 16 q24 ∷
   rw 13 q26 ∷
   rw 14 q27 ∷
   rw 15 q26 ∷
   rw 12 q26 ∷
   rw 13 q27 ∷
   rw 14 q26 ∷
   rw 11 q26 ∷
   rw 12 q27 ∷
   rw 13 q26 ∷
   rw 10 q33 ∷
   rw 11 q34 ∷
   rw 12 q33 ∷
   rw 9 q24 ∷
   rw 10 q25 ∷
   rw 11 q24 ∷
   rw 8 q33 ∷
   rw 9 q34 ∷
   rw 10 q33 ∷
   rw 7 q24 ∷
   rw 8 q25 ∷
   rw 9 q24 ∷
   rw 10 q1 ∷
   rw⁻ 9 q28 ∷
   rw⁻ 8 q29 ∷
   rw⁻ 7 q28 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q6 ∷
   rw 7 q30 ∷
   rw⁻ 6 q6 ∷
   re 7 3 (ℓ "乓") ∷
   rw 7 q31 ∷
   rw 6 q28 ∷
   rw 7 q29 ∷
   rw 8 q28 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q6 ∷
   rw 10 q32 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q12 ∷
   rw 5 q35 ∷
   rw 4 q35 ∷
   rw 3 q36 ∷
   rw 2 q35 ∷
   rw 1 q36 ∷
   rw 0 q36 ∷ []) Eq.refl
