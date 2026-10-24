{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D427 (W : Ws) where

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
  q2 = wE 31 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 21 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q6 : Eqn
  q6 = wE 51 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = wE 629 W
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 1151 W
  q20 : Eqn
  q20 = wE 1036 W
  q21 : Eqn
  q21 = wE 1035 W
  q22 : Eqn
  q22 = wE 464 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CSd12 X2] part1: 500 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2-part1 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中丘乏丧並乏並丷丘中中中中乀中中中乑中中") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丠丠丠临丠丠乀中中中中中中乑乏且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乏") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2-part1 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中丘乏丧並乏並丷丘中中中中乀中中中乑中中") (ℓ "丘丷丘丠丠丠临丠丠乀中中中中中中乑乏且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乏")
  (rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q2 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q7 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q1 ∷
   rw 22 q10 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q11 ∷
   rw 21 q9 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q1 ∷
   rw 23 q12 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q2 ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q1 ∷
   rw 19 q10 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q11 ∷
   rw 18 q9 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q1 ∷
   rw 20 q12 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q2 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q7 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q8 ∷
   rw⁻ 21 q9 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q1 ∷
   rw 21 q10 ∷
   rw⁻ 20 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q11 ∷
   rw 20 q9 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q1 ∷
   rw 22 q12 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q2 ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q1 ∷
   rw 18 q10 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q11 ∷
   rw 17 q9 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q1 ∷
   rw 19 q12 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q2 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q7 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q1 ∷
   rw 20 q10 ∷
   rw⁻ 19 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q11 ∷
   rw 19 q9 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q1 ∷
   rw 21 q12 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q2 ∷
   rw 18 q8 ∷
   rw⁻ 17 q9 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q1 ∷
   rw 17 q10 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q11 ∷
   rw 16 q9 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q1 ∷
   rw 18 q12 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q2 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q7 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q1 ∷
   rw 19 q10 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q11 ∷
   rw 18 q9 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q1 ∷
   rw 20 q12 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q2 ∷
   rw 17 q8 ∷
   rw⁻ 16 q9 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q1 ∷
   rw 16 q10 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q11 ∷
   rw 15 q9 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q1 ∷
   rw 17 q12 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q2 ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   rw 17 q6 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q7 ∷
   re 17 5 (ℓ "中") ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q1 ∷
   rw 18 q10 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q11 ∷
   rw 17 q9 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q1 ∷
   rw 19 q12 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q2 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 16 q13 ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q1 ∷
   rw 14 q15 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (ℓ "乔") ∷
   rw 14 q16 ∷
   rw 13 q9 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q1 ∷
   rw 15 q17 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q2 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q4 ∷
   rw 16 q18 ∷
   rw 15 q6 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q7 ∷
   re 15 5 (ℓ "乑") ∷
   rw 17 q8 ∷
   rw⁻ 16 q9 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q1 ∷
   rw 16 q15 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (ℓ "乔") ∷
   rw 16 q16 ∷
   rw 15 q9 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q1 ∷
   rw 17 q17 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q2 ∷
   rw 14 q8 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q10 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q11 ∷
   rw 12 q9 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q1 ∷
   rw 14 q12 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q2 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q4 ∷
   rw 15 q5 ∷
   rw 14 q6 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q7 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q1 ∷
   rw 15 q10 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q11 ∷
   rw 14 q9 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q1 ∷
   rw 16 q12 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q2 ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q1 ∷
   rw 12 q10 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q11 ∷
   rw 11 q9 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q1 ∷
   rw 13 q12 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q2 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q7 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q1 ∷
   rw 14 q10 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q11 ∷
   rw 13 q9 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q1 ∷
   rw 15 q12 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q2 ∷
   rw 12 q8 ∷
   rw⁻ 11 q9 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q1 ∷
   rw 11 q10 ∷
   rw⁻ 10 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q11 ∷
   rw 10 q9 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q1 ∷
   rw 12 q12 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q2 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q7 ∷
   re 12 5 (ℓ "中") ∷
   rw 14 q8 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q10 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q11 ∷
   rw 12 q9 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q1 ∷
   rw 14 q12 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q2 ∷
   rw 11 q8 ∷
   rw⁻ 10 q9 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q1 ∷
   rw 10 q10 ∷
   rw⁻ 9 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q11 ∷
   rw 9 q9 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q1 ∷
   rw 11 q12 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q7 ∷
   re 11 5 (ℓ "中") ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q1 ∷
   rw 12 q10 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q11 ∷
   rw 11 q9 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q1 ∷
   rw 13 q12 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q2 ∷
   rw 10 q8 ∷
   rw⁻ 9 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q1 ∷
   rw 9 q10 ∷
   rw⁻ 8 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q11 ∷
   rw 8 q9 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q1 ∷
   rw 10 q12 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q2 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q7 ∷
   re 10 5 (ℓ "中") ∷
   rw 12 q8 ∷
   rw⁻ 11 q9 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q1 ∷
   rw 11 q10 ∷
   rw⁻ 10 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q11 ∷
   rw 10 q9 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q1 ∷
   rw 12 q12 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q2 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q1 ∷
   rw 8 q10 ∷
   rw⁻ 7 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw 8 q11 ∷
   rw 7 q9 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q1 ∷
   rw 9 q12 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q7 ∷
   re 9 5 (ℓ "中") ∷
   rw 11 q8 ∷
   rw⁻ 10 q9 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q1 ∷
   rw 10 q10 ∷
   rw⁻ 9 q1 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q11 ∷
   rw 9 q9 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q1 ∷
   rw 11 q12 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q2 ∷
   rw 6 q19 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q20 ∷
   rw 0 q20 ∷
   rw 34 q3 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q7 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q7 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q7 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q7 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q7 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q7 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 29 q7 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q7 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q7 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q7 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q7 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q7 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q7 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q7 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q7 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q7 ∷
   rw 17 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q24 : Eqn
  q24 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q25 : Eqn
  q25 = wE 656 W
  q26 : Eqn
  q26 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CSd12 X2] part2: 63 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2-part2 : ⟪ (ℓ "丘丷丘丠丠丠临丠丠乀中中中中中中乑乏且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乏") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2-part2 = derive (ℓ "丘丷丘丠丠丠临丠丠乀中中中中中中乑乏且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧乏") (ℓ "丘丷丘中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q7 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q7 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q7 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q7 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q7 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q7 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q7 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q7 ∷
   rw 8 q23 ∷
   rw 7 q23 ∷
   rw 6 q24 ∷
   rw 5 q23 ∷
   rw 4 q23 ∷
   rw 3 q23 ∷
   rw 4 q25 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q23 ∷
   rw⁻ 12 q23 ∷
   rw⁻ 13 q23 ∷
   rw⁻ 14 q23 ∷
   rw⁻ 15 q23 ∷
   rw⁻ 16 q24 ∷
   rw⁻ 17 q26 ∷
   rw⁻ 18 q23 ∷
   rw⁻ 19 q23 ∷
   rw⁻ 20 q23 ∷
   rw⁻ 21 q23 ∷
   rw⁻ 22 q23 ∷
   rw⁻ 23 q23 ∷
   rw⁻ 24 q23 ∷
   rw⁻ 25 q23 ∷
   rw⁻ 26 q23 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q23 ∷
   rw⁻ 29 q23 ∷
   rw⁻ 30 q23 ∷
   rw⁻ 31 q24 ∷
   rw⁻ 32 q23 ∷
   rw⁻ 33 q23 ∷
   rw 34 q7 ∷ []) Eq.refl
