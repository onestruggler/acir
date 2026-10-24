{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D469 (W : Ws) where

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
  q1 = eqn (ℓ "丌乇") (ℓ "乇丌") (low₁-comm (X) (CK₁₀))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 279 W
  q4 : Eqn
  q4 = eqn (ℓ "严乗") (ℓ "乗严") (low-comm ((S • CK₀₁)) (CK₁₀))
  q5 : Eqn
  q5 = wE 280 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q8 : Eqn
  q8 = wE 65 W
  q9 : Eqn
  q9 = eqn (ℓ "严义") (ℓ "义严") (low-comm ((S • CK₀₁)) (CS))
  q10 : Eqn
  q10 = wE 48 W
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = wE 1106 W
  q13 : Eqn
  q13 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 1228 W
  q15 : Eqn
  q15 = wE 74 W
  q16 : Eqn
  q16 = wE 918 W
  q17 : Eqn
  q17 = wE 317 W
  q18 : Eqn
  q18 = wE 330 W
  q19 : Eqn
  q19 = wE 30 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = eqn (ℓ "丌且") (ℓ "且丌") (low₁-comm (X) ((S ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q23 : Eqn
  q23 = wE 706 W
  q24 : Eqn
  q24 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q26 : Eqn
  q26 = wE 1229 W
  q27 : Eqn
  q27 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q28 : Eqn
  q28 = wE 1230 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21] [X0 CKd03 X0]: 365 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-X0-CKd03-X0 : ⟪ (ℓ "丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌串丌") ⟫ʷ ≈ ⟪ (ℓ "丌串丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-vs-X0-CKd03-X0 = derive (ℓ "丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌串丌") (ℓ "丌串丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇")
  (rw⁻ 28 q1 ∷
   re 30 1 (ℓ "乏丼严丼乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "乔") ∷
   rw 30 q3 ∷
   rw⁻ 31 q4 ∷
   rw 32 q5 ∷
   re 33 1 (ℓ "乏乇乏") ∷
   rw 35 q6 ∷
   re 29 5 (ℓ "串") ∷
   rw⁻ 30 q1 ∷
   rw⁻ 27 q1 ∷
   re 29 1 (ℓ "乏丼严丼乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "乔") ∷
   rw 29 q3 ∷
   rw⁻ 30 q4 ∷
   rw 31 q5 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 34 q6 ∷
   re 28 5 (ℓ "串") ∷
   rw⁻ 29 q1 ∷
   rw⁻ 26 q7 ∷
   re 28 1 (ℓ "乏丼严丼乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q8 ∷
   rw⁻ 29 q9 ∷
   rw 30 q10 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q6 ∷
   re 27 5 (ℓ "串") ∷
   rw⁻ 28 q7 ∷
   rw⁻ 25 q1 ∷
   re 27 1 (ℓ "乏丼严丼乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "乔") ∷
   rw 27 q3 ∷
   rw⁻ 28 q4 ∷
   rw 29 q5 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 32 q6 ∷
   re 26 5 (ℓ "串") ∷
   rw⁻ 27 q1 ∷
   rw⁻ 24 q7 ∷
   re 26 1 (ℓ "乏丼严丼乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q8 ∷
   rw⁻ 27 q9 ∷
   rw 28 q10 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q6 ∷
   re 25 5 (ℓ "串") ∷
   rw⁻ 26 q7 ∷
   rw⁻ 23 q7 ∷
   re 25 1 (ℓ "乏丼严丼乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q8 ∷
   rw⁻ 26 q9 ∷
   rw 27 q10 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 30 q6 ∷
   re 24 5 (ℓ "串") ∷
   rw⁻ 25 q7 ∷
   rw 26 q11 ∷
   rw 25 q12 ∷
   re 24 1 (ℓ "乏丬乏") ∷
   rw⁻ 26 q13 ∷
   rw 25 q14 ∷
   rw⁻ 24 q13 ∷
   re 25 3 (ℓ "乂") ∷
   rw 23 q12 ∷
   rw 22 q15 ∷
   rw 23 q16 ∷
   rw 22 q17 ∷
   re 24 1 (ℓ "乏主乏") ∷
   rw 23 q13 ∷
   rw 24 q18 ∷
   rw 25 q13 ∷
   re 23 3 (ℓ "串") ∷
   rw 24 q17 ∷
   rw 25 q19 ∷
   rw 26 q20 ∷
   rw⁻ 21 q7 ∷
   re 23 1 (ℓ "乏丼严丼乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q8 ∷
   rw⁻ 24 q9 ∷
   rw 25 q10 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q6 ∷
   re 22 5 (ℓ "串") ∷
   rw⁻ 23 q7 ∷
   rw⁻ 20 q7 ∷
   re 22 1 (ℓ "乏丼严丼乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q8 ∷
   rw⁻ 23 q9 ∷
   rw 24 q10 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 27 q6 ∷
   re 21 5 (ℓ "串") ∷
   rw⁻ 22 q7 ∷
   rw⁻ 19 q7 ∷
   re 21 1 (ℓ "乏丼严丼乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q8 ∷
   rw⁻ 22 q9 ∷
   rw 23 q10 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q6 ∷
   re 20 5 (ℓ "串") ∷
   rw⁻ 21 q7 ∷
   rw⁻ 18 q7 ∷
   re 20 1 (ℓ "乏丼严丼乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q8 ∷
   rw⁻ 21 q9 ∷
   rw 22 q10 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q6 ∷
   re 19 5 (ℓ "串") ∷
   rw⁻ 20 q7 ∷
   rw⁻ 17 q7 ∷
   re 19 1 (ℓ "乏丼严丼乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q8 ∷
   rw⁻ 20 q9 ∷
   rw 21 q10 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q6 ∷
   re 18 5 (ℓ "串") ∷
   rw⁻ 19 q7 ∷
   rw⁻ 16 q7 ∷
   re 18 1 (ℓ "乏丼严丼乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q8 ∷
   rw⁻ 19 q9 ∷
   rw 20 q10 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q6 ∷
   re 17 5 (ℓ "串") ∷
   rw⁻ 18 q7 ∷
   rw⁻ 15 q21 ∷
   rw 18 q11 ∷
   re 17 1 (ℓ "乏丬乏") ∷
   rw⁻ 19 q13 ∷
   rw 18 q14 ∷
   rw⁻ 17 q13 ∷
   re 18 3 (ℓ "乂") ∷
   rw⁻ 16 q22 ∷
   rw 17 q23 ∷
   re 17 1 (ℓ "乏主乏") ∷
   rw 16 q13 ∷
   rw 17 q18 ∷
   rw 18 q13 ∷
   re 16 3 (ℓ "串") ∷
   rw 17 q22 ∷
   rw 18 q20 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 14 q1 ∷
   re 16 1 (ℓ "乏丼严丼乏") ∷
   rw 15 q2 ∷
   re 16 3 (ℓ "乔") ∷
   rw 16 q3 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 21 q6 ∷
   re 15 5 (ℓ "串") ∷
   rw⁻ 16 q1 ∷
   rw⁻ 13 q7 ∷
   re 15 1 (ℓ "乏丼严丼乏") ∷
   rw 14 q2 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q8 ∷
   rw⁻ 16 q9 ∷
   rw 17 q10 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q6 ∷
   re 14 5 (ℓ "串") ∷
   rw⁻ 15 q7 ∷
   rw⁻ 12 q7 ∷
   re 14 1 (ℓ "乏丼严丼乏") ∷
   rw 13 q2 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q8 ∷
   rw⁻ 15 q9 ∷
   rw 16 q10 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q6 ∷
   re 13 5 (ℓ "串") ∷
   rw⁻ 14 q7 ∷
   rw⁻ 11 q7 ∷
   re 13 1 (ℓ "乏丼严丼乏") ∷
   rw 12 q2 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q8 ∷
   rw⁻ 14 q9 ∷
   rw 15 q10 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q6 ∷
   re 12 5 (ℓ "串") ∷
   rw⁻ 13 q7 ∷
   rw⁻ 10 q21 ∷
   rw 13 q11 ∷
   re 12 1 (ℓ "乏丬乏") ∷
   rw⁻ 14 q13 ∷
   rw 13 q14 ∷
   rw⁻ 12 q13 ∷
   re 13 3 (ℓ "乂") ∷
   rw⁻ 11 q22 ∷
   rw 12 q23 ∷
   re 12 1 (ℓ "乏主乏") ∷
   rw 11 q13 ∷
   rw 12 q18 ∷
   rw 13 q13 ∷
   re 11 3 (ℓ "串") ∷
   rw 12 q22 ∷
   rw 13 q20 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 9 q1 ∷
   re 11 1 (ℓ "乏丼严丼乏") ∷
   rw 10 q2 ∷
   re 11 3 (ℓ "乔") ∷
   rw 11 q3 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q6 ∷
   re 10 5 (ℓ "串") ∷
   rw⁻ 11 q1 ∷
   rw⁻ 8 q21 ∷
   rw 11 q11 ∷
   re 10 1 (ℓ "乏丬乏") ∷
   rw⁻ 12 q13 ∷
   rw 11 q14 ∷
   rw⁻ 10 q13 ∷
   re 11 3 (ℓ "乂") ∷
   rw⁻ 9 q22 ∷
   rw 10 q23 ∷
   re 10 1 (ℓ "乏主乏") ∷
   rw 9 q13 ∷
   rw 10 q18 ∷
   rw 11 q13 ∷
   re 9 3 (ℓ "串") ∷
   rw 10 q22 ∷
   rw 11 q20 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 7 q1 ∷
   re 9 1 (ℓ "乏丼严丼乏") ∷
   rw 8 q2 ∷
   re 9 3 (ℓ "乔") ∷
   rw 9 q3 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 14 q6 ∷
   re 8 5 (ℓ "串") ∷
   rw⁻ 9 q1 ∷
   rw 10 q11 ∷
   rw 9 q12 ∷
   re 8 1 (ℓ "乏丬乏") ∷
   rw⁻ 10 q13 ∷
   rw 9 q14 ∷
   rw⁻ 8 q13 ∷
   re 9 3 (ℓ "乂") ∷
   rw 7 q12 ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 6 q17 ∷
   re 8 1 (ℓ "乏主乏") ∷
   rw 7 q13 ∷
   rw 8 q18 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "串") ∷
   rw 8 q17 ∷
   rw 9 q19 ∷
   rw 10 q20 ∷
   rw 9 q2 ∷
   rw 8 q24 ∷
   re 7 1 (ℓ "乏丬乏") ∷
   rw 9 q6 ∷
   rw 6 q24 ∷
   rw 5 q25 ∷
   rw 6 q26 ∷
   rw⁻ 5 q24 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "串") ∷
   rw⁻ 7 q24 ∷
   rw⁻ 8 q25 ∷
   rw 9 q6 ∷
   rw 8 q2 ∷
   rw 7 q24 ∷
   re 6 1 (ℓ "乏丬乏") ∷
   rw 8 q6 ∷
   rw 5 q24 ∷
   rw 4 q25 ∷
   rw 5 q26 ∷
   rw⁻ 4 q24 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "串") ∷
   rw⁻ 6 q24 ∷
   rw⁻ 7 q25 ∷
   rw 8 q6 ∷
   rw 7 q2 ∷
   rw 6 q24 ∷
   re 5 1 (ℓ "乏丬乏") ∷
   rw 7 q6 ∷
   rw 4 q24 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷
   rw⁻ 3 q24 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "串") ∷
   rw⁻ 5 q24 ∷
   rw⁻ 6 q27 ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   rw 5 q24 ∷
   re 4 1 (ℓ "乏丬乏") ∷
   rw 6 q6 ∷
   rw 3 q24 ∷
   rw 2 q25 ∷
   rw 3 q26 ∷
   rw⁻ 2 q24 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "串") ∷
   rw⁻ 4 q24 ∷
   rw⁻ 5 q25 ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   rw 4 q24 ∷
   re 3 1 (ℓ "乏丬乏") ∷
   rw 5 q6 ∷
   rw 2 q24 ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw⁻ 1 q24 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "串") ∷
   rw⁻ 3 q24 ∷
   rw⁻ 4 q27 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   rw 3 q24 ∷
   re 2 1 (ℓ "乏丬乏") ∷
   rw 4 q6 ∷
   rw 1 q24 ∷
   rw 0 q27 ∷
   rw 1 q28 ∷
   rw⁻ 0 q24 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "串") ∷
   rw⁻ 2 q24 ∷
   rw⁻ 3 q27 ∷
   rw 4 q6 ∷ []) Eq.refl
