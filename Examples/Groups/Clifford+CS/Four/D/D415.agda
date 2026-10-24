{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D415 (W : Ws) where

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
  q2 = wE 27 W
  q3 : Eqn
  q3 = wE 31 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 20 W
  q6 : Eqn
  q6 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q7 : Eqn
  q7 = wE 49 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 629 W
  q13 : Eqn
  q13 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (ℓ "丶业") (ℓ "业丶") (low₃-comm ((CS ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X2 CS12 X2] part1: 500 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CS12-X2-part1 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中丘並乏丶乏並丶丘中中乌中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丧丧丧乄丧丧乌中丘丶丘中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CS12-X2-part1 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中丘並乏丶乏並丶丘中中乌中中中乑中中") (ℓ "丧丧丧乄丧丧乌中丘丶丘中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q3 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q7 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q8 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q9 ∷
   rw⁻ 24 q10 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q1 ∷
   rw 24 q11 ∷
   rw⁻ 23 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q12 ∷
   rw 23 q10 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q1 ∷
   rw 25 q2 ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q3 ∷
   rw 22 q9 ∷
   rw⁻ 21 q10 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q1 ∷
   rw 21 q11 ∷
   rw⁻ 20 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q12 ∷
   rw 20 q10 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q3 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q8 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q9 ∷
   rw⁻ 23 q10 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q1 ∷
   rw 23 q11 ∷
   rw⁻ 22 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q12 ∷
   rw 22 q10 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q3 ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q1 ∷
   rw 20 q11 ∷
   rw⁻ 19 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q12 ∷
   rw 19 q10 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q3 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q8 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q9 ∷
   rw⁻ 22 q10 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q1 ∷
   rw 22 q11 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q12 ∷
   rw 21 q10 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q3 ∷
   rw 20 q9 ∷
   rw⁻ 19 q10 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q1 ∷
   rw 19 q11 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q12 ∷
   rw 18 q10 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q3 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   rw 20 q7 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q8 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q9 ∷
   rw⁻ 21 q10 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q1 ∷
   rw 21 q11 ∷
   rw⁻ 20 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q12 ∷
   rw 20 q10 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q3 ∷
   rw 19 q9 ∷
   rw⁻ 18 q10 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q1 ∷
   rw 18 q11 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q12 ∷
   rw 17 q10 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q3 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q7 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q8 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q1 ∷
   rw 20 q11 ∷
   rw⁻ 19 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q12 ∷
   rw 19 q10 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q3 ∷
   rw 18 q9 ∷
   rw⁻ 17 q10 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q1 ∷
   rw 17 q11 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q12 ∷
   rw 16 q10 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q1 ∷
   rw 18 q2 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q3 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q7 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q8 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q9 ∷
   rw⁻ 19 q10 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q1 ∷
   rw 19 q11 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q12 ∷
   rw 18 q10 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q3 ∷
   rw 17 q9 ∷
   rw⁻ 16 q10 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q1 ∷
   rw 16 q11 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q12 ∷
   rw 15 q10 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q1 ∷
   rw 17 q2 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q3 ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   rw 17 q7 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q8 ∷
   re 17 5 (ℓ "中") ∷
   rw 19 q9 ∷
   rw⁻ 18 q10 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q1 ∷
   rw 18 q11 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q12 ∷
   rw 17 q10 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q3 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 16 q13 ∷
   rw 15 q9 ∷
   rw⁻ 14 q10 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q1 ∷
   rw 14 q15 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (ℓ "乔") ∷
   rw 14 q16 ∷
   rw 13 q10 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q1 ∷
   rw 15 q17 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q3 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q4 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q5 ∷
   rw 16 q18 ∷
   rw 15 q7 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q8 ∷
   re 15 5 (ℓ "乑") ∷
   rw 17 q9 ∷
   rw⁻ 16 q10 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q1 ∷
   rw 16 q15 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (ℓ "乔") ∷
   rw 16 q16 ∷
   rw 15 q10 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q1 ∷
   rw 17 q17 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q3 ∷
   rw 14 q9 ∷
   rw⁻ 13 q10 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q11 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q12 ∷
   rw 12 q10 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q1 ∷
   rw 14 q2 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q4 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q7 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q8 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q9 ∷
   rw⁻ 15 q10 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q1 ∷
   rw 15 q11 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q12 ∷
   rw 14 q10 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q1 ∷
   rw 16 q2 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q3 ∷
   rw 13 q9 ∷
   rw⁻ 12 q10 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q1 ∷
   rw 12 q11 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q12 ∷
   rw 11 q10 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q1 ∷
   rw 13 q2 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q3 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q5 ∷
   rw 14 q6 ∷
   rw 13 q7 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q8 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q9 ∷
   rw⁻ 14 q10 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q1 ∷
   rw 14 q11 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q12 ∷
   rw 13 q10 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q3 ∷
   rw 12 q9 ∷
   rw⁻ 11 q10 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q1 ∷
   rw 11 q11 ∷
   rw⁻ 10 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q12 ∷
   rw 10 q10 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q1 ∷
   rw 12 q2 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q3 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q4 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q8 ∷
   re 12 5 (ℓ "中") ∷
   rw 14 q9 ∷
   rw⁻ 13 q10 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q11 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q12 ∷
   rw 12 q10 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q1 ∷
   rw 14 q2 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q3 ∷
   rw 11 q9 ∷
   rw⁻ 10 q10 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q1 ∷
   rw 10 q11 ∷
   rw⁻ 9 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q12 ∷
   rw 9 q10 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q1 ∷
   rw 11 q2 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q3 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q4 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q8 ∷
   re 11 5 (ℓ "中") ∷
   rw 13 q9 ∷
   rw⁻ 12 q10 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q1 ∷
   rw 12 q11 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q12 ∷
   rw 11 q10 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q1 ∷
   rw 13 q2 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q3 ∷
   rw 10 q9 ∷
   rw⁻ 9 q10 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q1 ∷
   rw 9 q11 ∷
   rw⁻ 8 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q12 ∷
   rw 8 q10 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q4 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q8 ∷
   re 10 5 (ℓ "中") ∷
   rw 12 q9 ∷
   rw⁻ 11 q10 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q1 ∷
   rw 11 q11 ∷
   rw⁻ 10 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q12 ∷
   rw 10 q10 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q1 ∷
   rw 12 q2 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q3 ∷ []) Eq.refl
