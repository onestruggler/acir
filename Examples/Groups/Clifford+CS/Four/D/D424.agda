{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D424 (W : Ws) where

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
  q2 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = wE 655 W
  q7 : Eqn
  q7 = wE 151 W
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 629 W
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 20 W
  q16 : Eqn
  q16 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q17 : Eqn
  q17 = wE 49 W
  q18 : Eqn
  q18 = wE 140 W
  q19 : Eqn
  q19 = wE 630 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q22 : Eqn
  q22 = wE 1150 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS12 X2] part0: 500 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2-part0 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中丘乏丧並乏並丶丘中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2-part0 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丶丘") (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中丘乏丧並乏並丶丘中中中中乀中中中乑中中")
  (rw 31 q1 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q2 ∷
   rw 26 q2 ∷
   rw 25 q2 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   rw 23 q2 ∷
   rw 22 q2 ∷
   rw 21 q2 ∷
   rw 20 q2 ∷
   rw 19 q2 ∷
   rw 18 q2 ∷
   rw 17 q2 ∷
   rw 16 q2 ∷
   rw 15 q2 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   rw 12 q2 ∷
   rw 11 q2 ∷
   rw 10 q2 ∷
   rw 9 q2 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q6 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q2 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q7 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乀") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q4 ∷
   rw 32 q8 ∷
   rw⁻ 31 q9 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q10 ∷
   rw 31 q11 ∷
   rw⁻ 30 q10 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q12 ∷
   rw 30 q9 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q10 ∷
   rw 32 q13 ∷
   rw 33 q10 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q14 ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "丽") ∷
   rw 34 q15 ∷
   rw 33 q16 ∷
   rw 32 q17 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q4 ∷
   re 32 5 (ℓ "中") ∷
   rw 34 q8 ∷
   rw⁻ 33 q9 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q10 ∷
   rw 33 q11 ∷
   rw⁻ 32 q10 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q12 ∷
   rw 32 q9 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q10 ∷
   rw 34 q13 ∷
   rw 35 q10 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q14 ∷
   rw 31 q8 ∷
   rw⁻ 30 q9 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q10 ∷
   rw 30 q11 ∷
   rw⁻ 29 q10 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q12 ∷
   rw 29 q9 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q10 ∷
   rw 31 q13 ∷
   rw 32 q10 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q14 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丽") ∷
   rw 33 q15 ∷
   rw 32 q16 ∷
   rw 31 q17 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q8 ∷
   rw⁻ 32 q9 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q10 ∷
   rw 32 q11 ∷
   rw⁻ 31 q10 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q12 ∷
   rw 31 q9 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q10 ∷
   rw 33 q13 ∷
   rw 34 q10 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q14 ∷
   rw 30 q8 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q10 ∷
   rw 29 q18 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (ℓ "乔") ∷
   rw 29 q19 ∷
   rw 28 q9 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q10 ∷
   rw 30 q20 ∷
   rw 31 q10 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q14 ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q15 ∷
   rw 31 q21 ∷
   rw 30 q17 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "乑") ∷
   rw 32 q8 ∷
   rw⁻ 31 q9 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q10 ∷
   rw 31 q18 ∷
   rw⁻ 30 q10 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q19 ∷
   rw 30 q9 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q10 ∷
   rw 32 q20 ∷
   rw 33 q10 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q14 ∷
   rw 29 q8 ∷
   rw⁻ 28 q9 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q10 ∷
   rw 28 q11 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q12 ∷
   rw 27 q9 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q10 ∷
   rw 29 q13 ∷
   rw 30 q10 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q14 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q15 ∷
   rw 30 q16 ∷
   rw 29 q17 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q4 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q8 ∷
   rw⁻ 30 q9 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q10 ∷
   rw 30 q11 ∷
   rw⁻ 29 q10 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q12 ∷
   rw 29 q9 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q10 ∷
   rw 31 q13 ∷
   rw 32 q10 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q14 ∷
   rw 28 q8 ∷
   rw⁻ 27 q9 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q10 ∷
   rw 27 q11 ∷
   rw⁻ 26 q10 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q12 ∷
   rw 26 q9 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q10 ∷
   rw 28 q13 ∷
   rw 29 q10 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q14 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q15 ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q8 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q10 ∷
   rw 29 q11 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q12 ∷
   rw 28 q9 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q10 ∷
   rw 30 q13 ∷
   rw 31 q10 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q14 ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q10 ∷
   rw 26 q11 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q12 ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q10 ∷
   rw 27 q13 ∷
   rw 28 q10 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q14 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   rw 27 q17 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q8 ∷
   rw⁻ 28 q9 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q10 ∷
   rw 28 q11 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q12 ∷
   rw 27 q9 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q10 ∷
   rw 29 q13 ∷
   rw 30 q10 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q14 ∷
   rw 24 q22 ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q10 ∷
   rw 24 q11 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q12 ∷
   rw 23 q9 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q10 ∷
   rw 25 q13 ∷
   rw 26 q10 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q14 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q15 ∷
   rw 26 q16 ∷
   rw 25 q17 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q4 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q10 ∷
   rw 26 q11 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q12 ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q10 ∷
   rw 27 q13 ∷
   rw 28 q10 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q14 ∷
   rw 24 q8 ∷
   rw⁻ 23 q9 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q10 ∷
   rw 23 q11 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q12 ∷
   rw 22 q9 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q10 ∷
   rw 24 q13 ∷
   rw 25 q10 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q14 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q15 ∷
   rw 25 q16 ∷
   rw 24 q17 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q4 ∷
   re 24 5 (ℓ "中") ∷
   rw 26 q8 ∷
   rw⁻ 25 q9 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q10 ∷
   rw 25 q11 ∷
   rw⁻ 24 q10 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q12 ∷
   rw 24 q9 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q10 ∷
   rw 26 q13 ∷
   rw 27 q10 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q14 ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q10 ∷
   rw 22 q11 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q12 ∷
   rw 21 q9 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q10 ∷
   rw 23 q13 ∷
   rw 24 q10 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q14 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q15 ∷
   rw 24 q16 ∷
   rw 23 q17 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q4 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q10 ∷
   rw 24 q11 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q12 ∷
   rw 23 q9 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q10 ∷
   rw 25 q13 ∷
   rw 26 q10 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q14 ∷
   rw 22 q8 ∷
   rw⁻ 21 q9 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q10 ∷
   rw 21 q11 ∷
   rw⁻ 20 q10 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q12 ∷
   rw 20 q9 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q10 ∷
   rw 22 q13 ∷
   rw 23 q10 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q14 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q15 ∷
   rw 23 q16 ∷
   rw 22 q17 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q4 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q8 ∷
   rw⁻ 23 q9 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q10 ∷
   rw 23 q11 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q12 ∷
   rw 22 q9 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q10 ∷
   rw 24 q13 ∷
   rw 25 q10 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q14 ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q10 ∷
   rw 20 q11 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q12 ∷
   rw 19 q9 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q10 ∷
   rw 21 q13 ∷ []) Eq.refl
