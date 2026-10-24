{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D421 (W : Ws) where

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
  q2 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = wE 583 W
  q7 : Eqn
  q7 = wE 151 W
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 140 W
  q12 : Eqn
  q12 = wE 630 W
  q13 : Eqn
  q13 = wE 142 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = wE 21 W
  q16 : Eqn
  q16 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q17 : Eqn
  q17 = wE 51 W
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = wE 629 W
  q20 : Eqn
  q20 = wE 27 W
  q21 : Eqn
  q21 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q22 : Eqn
  q22 = wE 1151 W
  q23 : Eqn
  q23 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q24 : Eqn
  q24 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q25 : Eqn
  q25 = wE 1035 W
  q26 : Eqn
  q26 = wE 1036 W
  q27 : Eqn
  q27 = wE 464 W
  q28 : Eqn
  q28 = wE 586 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CSd12 X2]: 897 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丘丷丘") (ℓ "丘丷丘中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   rw 8 q5 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q6 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q2 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q7 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q7 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q7 ∷
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
   re 22 3 (ℓ "乀") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乑") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乑") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q4 ∷
   rw 30 q8 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q10 ∷
   rw 29 q11 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (ℓ "乔") ∷
   rw 29 q12 ∷
   rw 28 q9 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q10 ∷
   rw 30 q13 ∷
   rw 31 q10 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q14 ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "乑") ∷
   rw 32 q8 ∷
   rw⁻ 31 q9 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q10 ∷
   rw 31 q11 ∷
   rw⁻ 30 q10 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q12 ∷
   rw 30 q9 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q10 ∷
   rw 32 q13 ∷
   rw 33 q10 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q14 ∷
   rw 29 q8 ∷
   rw⁻ 28 q9 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q10 ∷
   rw 28 q11 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (ℓ "乔") ∷
   rw 28 q12 ∷
   rw 27 q9 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q10 ∷
   rw 29 q13 ∷
   rw 30 q10 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q14 ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q15 ∷
   rw 30 q16 ∷
   rw 29 q17 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q4 ∷
   re 29 5 (ℓ "乑") ∷
   rw 31 q8 ∷
   rw⁻ 30 q9 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw⁻ 31 q10 ∷
   rw 30 q11 ∷
   rw⁻ 29 q10 ∷
   re 30 3 (ℓ "乔") ∷
   rw 30 q12 ∷
   rw 29 q9 ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q10 ∷
   rw 31 q13 ∷
   rw 32 q10 ∷
   re 30 3 (ℓ "乑") ∷
   rw 31 q14 ∷
   rw 28 q8 ∷
   rw⁻ 27 q9 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q10 ∷
   rw 27 q18 ∷
   rw⁻ 26 q10 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q19 ∷
   rw 26 q9 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q10 ∷
   rw 28 q20 ∷
   rw 29 q10 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q14 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q15 ∷
   rw 29 q21 ∷
   rw 28 q17 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q8 ∷
   rw⁻ 29 q9 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q10 ∷
   rw 29 q18 ∷
   rw⁻ 28 q10 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q19 ∷
   rw 28 q9 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q10 ∷
   rw 30 q20 ∷
   rw 31 q10 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q14 ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q10 ∷
   rw 26 q11 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (ℓ "乔") ∷
   rw 26 q12 ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q10 ∷
   rw 27 q13 ∷
   rw 28 q10 ∷
   re 26 3 (ℓ "乑") ∷
   rw 27 q14 ∷
   re 26 1 (ℓ "乏丼临丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   rw 27 q17 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "乑") ∷
   rw 29 q8 ∷
   rw⁻ 28 q9 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q10 ∷
   rw 28 q11 ∷
   rw⁻ 27 q10 ∷
   re 28 3 (ℓ "乔") ∷
   rw 28 q12 ∷
   rw 27 q9 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q10 ∷
   rw 29 q13 ∷
   rw 30 q10 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q14 ∷
   rw 26 q8 ∷
   rw⁻ 25 q9 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q10 ∷
   rw 25 q18 ∷
   rw⁻ 24 q10 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q19 ∷
   rw 24 q9 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q10 ∷
   rw 26 q20 ∷
   rw 27 q10 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q14 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q15 ∷
   rw 27 q21 ∷
   rw 26 q17 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q4 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q8 ∷
   rw⁻ 27 q9 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q10 ∷
   rw 27 q18 ∷
   rw⁻ 26 q10 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q19 ∷
   rw 26 q9 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q10 ∷
   rw 28 q20 ∷
   rw 29 q10 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q14 ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q10 ∷
   rw 24 q18 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q19 ∷
   rw 23 q9 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q10 ∷
   rw 25 q20 ∷
   rw 26 q10 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q14 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q15 ∷
   rw 26 q21 ∷
   rw 25 q17 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q4 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q8 ∷
   rw⁻ 26 q9 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q10 ∷
   rw 26 q18 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q19 ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q10 ∷
   rw 27 q20 ∷
   rw 28 q10 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q14 ∷
   rw 22 q22 ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q10 ∷
   rw 22 q18 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q19 ∷
   rw 21 q9 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q10 ∷
   rw 23 q20 ∷
   rw 24 q10 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q14 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q15 ∷
   rw 24 q21 ∷
   rw 23 q17 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q4 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q8 ∷
   rw⁻ 24 q9 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q10 ∷
   rw 24 q18 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q19 ∷
   rw 23 q9 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q10 ∷
   rw 25 q20 ∷
   rw 26 q10 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q14 ∷
   rw 22 q8 ∷
   rw⁻ 21 q9 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q10 ∷
   rw 21 q18 ∷
   rw⁻ 20 q10 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q19 ∷
   rw 20 q9 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q10 ∷
   rw 22 q20 ∷
   rw 23 q10 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q14 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q15 ∷
   rw 23 q21 ∷
   rw 22 q17 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q4 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q8 ∷
   rw⁻ 23 q9 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q10 ∷
   rw 23 q18 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q19 ∷
   rw 22 q9 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q10 ∷
   rw 24 q20 ∷
   rw 25 q10 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q14 ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q10 ∷
   rw 20 q18 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q19 ∷
   rw 19 q9 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q10 ∷
   rw 21 q20 ∷
   rw 22 q10 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q14 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q15 ∷
   rw 22 q21 ∷
   rw 21 q17 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q4 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q8 ∷
   rw⁻ 22 q9 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q10 ∷
   rw 22 q18 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q19 ∷
   rw 21 q9 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q10 ∷
   rw 23 q20 ∷
   rw 24 q10 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q14 ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q10 ∷
   rw 19 q18 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q19 ∷
   rw 18 q9 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q10 ∷
   rw 20 q20 ∷
   rw 21 q10 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q14 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q15 ∷
   rw 21 q21 ∷
   rw 20 q17 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q4 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q8 ∷
   rw⁻ 21 q9 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q10 ∷
   rw 21 q18 ∷
   rw⁻ 20 q10 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q19 ∷
   rw 20 q9 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q10 ∷
   rw 22 q20 ∷
   rw 23 q10 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q14 ∷
   rw 19 q8 ∷
   rw⁻ 18 q9 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q10 ∷
   rw 18 q18 ∷
   rw⁻ 17 q10 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q19 ∷
   rw 17 q9 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q10 ∷
   rw 19 q20 ∷
   rw 20 q10 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q14 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q15 ∷
   rw 20 q21 ∷
   rw 19 q17 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q4 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q8 ∷
   rw⁻ 20 q9 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q10 ∷
   rw 20 q18 ∷
   rw⁻ 19 q10 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q19 ∷
   rw 19 q9 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q10 ∷
   rw 21 q20 ∷
   rw 22 q10 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q14 ∷
   rw 18 q8 ∷
   rw⁻ 17 q9 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q10 ∷
   rw 17 q18 ∷
   rw⁻ 16 q10 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q19 ∷
   rw 16 q9 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q10 ∷
   rw 18 q20 ∷
   rw 19 q10 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q14 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q15 ∷
   rw 19 q21 ∷
   rw 18 q17 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q4 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q8 ∷
   rw⁻ 19 q9 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q10 ∷
   rw 19 q18 ∷
   rw⁻ 18 q10 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q19 ∷
   rw 18 q9 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q10 ∷
   rw 20 q20 ∷
   rw 21 q10 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q14 ∷
   rw⁻ 15 q23 ∷
   rw⁻ 16 q24 ∷
   rw⁻ 17 q23 ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q10 ∷
   rw 15 q11 ∷
   rw⁻ 14 q10 ∷
   re 15 3 (ℓ "乔") ∷
   rw 15 q12 ∷
   rw 14 q9 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q10 ∷
   rw 16 q13 ∷
   rw 17 q10 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q14 ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "举") ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q4 ∷
   re 16 5 (ℓ "乑") ∷
   rw 18 q8 ∷
   rw⁻ 17 q9 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw⁻ 18 q10 ∷
   rw 17 q11 ∷
   rw⁻ 16 q10 ∷
   re 17 3 (ℓ "乔") ∷
   rw 17 q12 ∷
   rw 16 q9 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q10 ∷
   rw 18 q13 ∷
   rw 19 q10 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q14 ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q10 ∷
   rw 14 q18 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q19 ∷
   rw 13 q9 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q10 ∷
   rw 15 q20 ∷
   rw 16 q10 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q14 ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q15 ∷
   rw 16 q21 ∷
   rw 15 q17 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q4 ∷
   re 15 5 (ℓ "中") ∷
   rw 17 q8 ∷
   rw⁻ 16 q9 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q10 ∷
   rw 16 q18 ∷
   rw⁻ 15 q10 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q19 ∷
   rw 15 q9 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q10 ∷
   rw 17 q20 ∷
   rw 18 q10 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q14 ∷
   rw 14 q8 ∷
   rw⁻ 13 q9 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q10 ∷
   rw 13 q18 ∷
   rw⁻ 12 q10 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q19 ∷
   rw 12 q9 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q10 ∷
   rw 14 q20 ∷
   rw 15 q10 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q14 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q15 ∷
   rw 15 q21 ∷
   rw 14 q17 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q4 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q8 ∷
   rw⁻ 15 q9 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q10 ∷
   rw 15 q18 ∷
   rw⁻ 14 q10 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q19 ∷
   rw 14 q9 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q10 ∷
   rw 16 q20 ∷
   rw 17 q10 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q14 ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q10 ∷
   rw 12 q18 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q19 ∷
   rw 11 q9 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q10 ∷
   rw 13 q20 ∷
   rw 14 q10 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q14 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q15 ∷
   rw 14 q21 ∷
   rw 13 q17 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q4 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q8 ∷
   rw⁻ 14 q9 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q10 ∷
   rw 14 q18 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q19 ∷
   rw 13 q9 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q10 ∷
   rw 15 q20 ∷
   rw 16 q10 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q14 ∷
   rw⁻ 10 q23 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q23 ∷
   rw 11 q8 ∷
   rw⁻ 10 q9 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q10 ∷
   rw 10 q11 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q12 ∷
   rw 9 q9 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q10 ∷
   rw 11 q13 ∷
   rw 12 q10 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q14 ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q15 ∷
   rw 12 q16 ∷
   rw 11 q17 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q4 ∷
   re 11 5 (ℓ "乑") ∷
   rw 13 q8 ∷
   rw⁻ 12 q9 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw⁻ 13 q10 ∷
   rw 12 q11 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (ℓ "乔") ∷
   rw 12 q12 ∷
   rw 11 q9 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q10 ∷
   rw 13 q13 ∷
   rw 14 q10 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q14 ∷
   rw⁻ 8 q23 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q23 ∷
   rw 9 q8 ∷
   rw⁻ 8 q9 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q10 ∷
   rw 8 q11 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (ℓ "乔") ∷
   rw 8 q12 ∷
   rw 7 q9 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q10 ∷
   rw 9 q13 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q15 ∷
   rw 10 q16 ∷
   rw 9 q17 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q4 ∷
   re 9 5 (ℓ "乑") ∷
   rw 11 q8 ∷
   rw⁻ 10 q9 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q10 ∷
   rw 10 q11 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q12 ∷
   rw 9 q9 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q10 ∷
   rw 11 q13 ∷
   rw 12 q10 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q14 ∷
   rw 6 q22 ∷
   rw 5 q25 ∷
   rw 4 q25 ∷
   rw 3 q26 ∷
   rw 2 q25 ∷
   rw 1 q26 ∷
   rw 0 q26 ∷
   rw 32 q1 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q4 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q4 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q4 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q4 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q4 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q4 ∷
   rw 18 q27 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q4 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q4 ∷
   rw 13 q27 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q4 ∷
   rw 11 q27 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q4 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q4 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   rw 6 q3 ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 3 q3 ∷
   rw 4 q28 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q3 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 22 q3 ∷
   rw⁻ 23 q3 ∷
   rw⁻ 24 q3 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q3 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 31 q2 ∷
   rw 32 q4 ∷ []) Eq.refl
