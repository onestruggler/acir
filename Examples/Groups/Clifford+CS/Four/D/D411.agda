{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D411 (W : Ws) where

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
  q1 = wE 629 W
  q2 : Eqn
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 27 W
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 20 W
  q10 : Eqn
  q10 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q11 : Eqn
  q11 = wE 49 W
  q12 : Eqn
  q12 = wE 3 W
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
  q19 : Eqn
  q19 = wE 754 W
  q20 : Eqn
  q20 = wE 511 W
  q21 : Eqn
  q21 = wE 512 W
  q22 : Eqn
  q22 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q23 : Eqn
  q23 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q24 : Eqn
  q24 = wE 517 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 CS12 X2] part1: 500 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part1 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中丘丶並乏丶乏丘並中中乌中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘中中乑中並乏乇乏乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇並") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part1 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中丘丶並乏丶乏丘並中中乌中中乑中乑乑") (ℓ "丘丶丘中中乑中並乏乇乏乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇並")
  (re 22 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q4 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q5 ∷
   rw 20 q6 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q7 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q1 ∷
   rw 18 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q5 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q8 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   rw 20 q11 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q12 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q6 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q7 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q5 ∷
   rw 19 q6 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q7 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q5 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q8 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   rw 19 q11 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q12 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q6 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q7 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q5 ∷
   rw 18 q6 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q7 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q5 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q8 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q11 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q12 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q6 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q7 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q1 ∷
   rw 18 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q5 ∷
   rw⁻ 15 q13 ∷
   rw⁻ 16 q14 ∷
   rw⁻ 17 q13 ∷
   rw 16 q6 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q15 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "乔") ∷
   rw 15 q16 ∷
   rw 14 q2 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q3 ∷
   rw 16 q17 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q5 ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q8 ∷
   re 19 3 (ℓ "丽") ∷
   rw 18 q9 ∷
   rw 17 q18 ∷
   rw 16 q11 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q12 ∷
   re 16 5 (ℓ "乑") ∷
   rw 18 q6 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q15 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (ℓ "乔") ∷
   rw 17 q16 ∷
   rw 16 q2 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q3 ∷
   rw 18 q17 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q5 ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q7 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q1 ∷
   rw 13 q2 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q5 ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q8 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   rw 15 q11 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q12 ∷
   re 15 5 (ℓ "中") ∷
   rw 17 q6 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q7 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q5 ∷
   rw 14 q6 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q7 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q1 ∷
   rw 12 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q5 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q8 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q12 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q6 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q7 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   rw 14 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   rw 16 q4 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q5 ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q7 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q5 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q8 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q12 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q7 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q1 ∷
   rw 13 q2 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q5 ∷
   rw⁻ 10 q13 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 12 q13 ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q15 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q16 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q3 ∷
   rw 11 q17 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q5 ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q8 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q9 ∷
   rw 12 q18 ∷
   rw 11 q11 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q12 ∷
   re 11 5 (ℓ "乑") ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q15 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "乔") ∷
   rw 12 q16 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q3 ∷
   rw 13 q17 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q5 ∷
   rw⁻ 8 q13 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q13 ∷
   rw 9 q6 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q3 ∷
   rw 8 q15 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (ℓ "乔") ∷
   rw 8 q16 ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q3 ∷
   rw 9 q17 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q5 ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "丽") ∷
   rw 11 q9 ∷
   rw 10 q18 ∷
   rw 9 q11 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q12 ∷
   re 9 5 (ℓ "乑") ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q15 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q16 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q3 ∷
   rw 11 q17 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q5 ∷
   rw 6 q19 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 32 q6 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q15 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "乔") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q15 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "乔") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q7 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q15 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q7 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q7 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   rw⁻ 25 q22 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q7 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q7 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q7 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q7 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q7 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q7 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   rw⁻ 18 q23 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q15 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "乔") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q7 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (ℓ "丽") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q7 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "丽") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q7 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 13 q23 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q15 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "乔") ∷
   rw⁻ 11 q23 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw⁻ 12 q3 ∷
   rw 11 q15 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (ℓ "乔") ∷
   rw⁻ 9 q22 ∷
   rw 8 q15 ∷
   rw 7 q15 ∷
   rw 6 q7 ∷
   rw 5 q15 ∷
   rw 4 q7 ∷
   rw 3 q7 ∷
   rw 4 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q3 ∷
   rw 6 q17 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏乇乏") ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q26 : Eqn
  q26 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 CS12 X2] part2: 33 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part2 : ⟪ (ℓ "丘丶丘中中乑中並乏乇乏乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇並") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part2 = derive (ℓ "丘丶丘中中乑中並乏乇乏乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇並") (ℓ "丘丶丘中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 7 q3 ∷
   rw 8 q17 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "乑") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q3 ∷
   rw 9 q17 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q25 ∷
   rw 10 q17 ∷
   rw 11 q26 ∷
   rw 12 q17 ∷
   rw 13 q26 ∷
   rw 14 q4 ∷
   rw 15 q4 ∷
   rw 16 q4 ∷
   rw 17 q17 ∷
   rw 18 q26 ∷
   rw 19 q4 ∷
   rw 20 q4 ∷
   rw 21 q4 ∷
   rw 22 q4 ∷
   rw 23 q4 ∷
   rw 24 q4 ∷
   rw 25 q25 ∷
   rw 26 q4 ∷
   rw 27 q4 ∷
   rw 28 q17 ∷
   rw 29 q4 ∷
   rw 30 q17 ∷
   rw 31 q17 ∷
   rw 32 q5 ∷ []) Eq.refl
