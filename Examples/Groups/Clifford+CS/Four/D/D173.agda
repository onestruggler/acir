{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D173 (W : Ws) where

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
  q2 = wE 7 W
  q3 : Eqn
  q3 = wE 629 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 21 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 51 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 360 W
  q13 : Eqn
  q13 = eqn (ℓ "丠乘") (ℓ "乘丠") (low-comm (CS) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = wE 362 W
  q15 : Eqn
  q15 = wE 20 W
  q16 : Eqn
  q16 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q17 : Eqn
  q17 = wE 49 W
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q20 : Eqn
  q20 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q21 : Eqn
  q21 = eqn (ℓ "么业") (ℓ "业么") (low₃-comm (((S ↑ • CK₁₀) ↑)) (S))
  q22 : Eqn
  q22 = eqn (ℓ "丶业") (ℓ "业丶") (low₃-comm ((CS ↑)) (S))
  q23 : Eqn
  q23 = wE 140 W
  q24 : Eqn
  q24 = wE 630 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q27 : Eqn
  q27 = eqn (ℓ "临乘") (ℓ "乘临") (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q28 : Eqn
  q28 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q29 : Eqn
  q29 = wE 751 W
  q30 : Eqn
  q30 = wE 752 W
  q31 : Eqn
  q31 = wE 753 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CSd12 CKd21 CS12 CS12 X2] part2: 214 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业乏丧乏並丘並丷么丶丶丘中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丘丷么丶丶丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd12-CKd21-CS12-CS12-X2-part2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业乏丧乏並丘並丷么丶丶丘中中乑业中中中中中中乌中中乑中乑乑") (ℓ "丘丷么丶丶丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw⁻ 13 q1 ∷
   rw 12 q2 ∷
   rw⁻ 11 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q1 ∷
   rw 13 q5 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q6 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "乕") ∷
   rw 16 q12 ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   re 14 1 (ℓ "乏么乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q7 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q15 ∷
   rw 16 q16 ∷
   rw 15 q17 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q11 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "丽") ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q11 ∷
   re 16 5 (ℓ "中") ∷
   rw 18 q18 ∷
   rw⁻ 17 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q1 ∷
   rw 17 q2 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q1 ∷
   rw 18 q5 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q6 ∷
   rw⁻ 10 q19 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q22 ∷
   rw⁻ 14 q22 ∷
   rw⁻ 15 q19 ∷
   rw 11 q18 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q1 ∷
   rw 10 q23 ∷
   rw⁻ 9 q1 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q24 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q1 ∷
   rw 11 q25 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q8 ∷
   rw 12 q26 ∷
   rw 11 q10 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q11 ∷
   re 11 5 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "乕") ∷
   rw 14 q12 ∷
   rw 13 q27 ∷
   rw 12 q14 ∷
   re 12 1 (ℓ "乏么乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丼临丼乏") ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q15 ∷
   rw 14 q28 ∷
   rw 13 q17 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q11 ∷
   re 13 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q15 ∷
   rw 15 q28 ∷
   rw 14 q17 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q11 ∷
   re 14 5 (ℓ "乑") ∷
   rw 16 q18 ∷
   rw⁻ 15 q4 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q1 ∷
   rw 15 q23 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (ℓ "乔") ∷
   rw 15 q24 ∷
   rw 14 q4 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q1 ∷
   rw 16 q25 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q6 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 9 q20 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q22 ∷
   rw⁻ 12 q22 ∷
   rw⁻ 13 q19 ∷
   rw 9 q18 ∷
   rw⁻ 8 q4 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q1 ∷
   rw 8 q23 ∷
   rw⁻ 7 q1 ∷
   re 8 3 (ℓ "乔") ∷
   rw 8 q24 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q1 ∷
   rw 9 q25 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q8 ∷
   rw 10 q26 ∷
   rw 9 q10 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q11 ∷
   re 9 5 (ℓ "乑") ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "乕") ∷
   rw 12 q12 ∷
   rw 11 q27 ∷
   rw 10 q14 ∷
   re 10 1 (ℓ "乏么乏") ∷
   rw 9 q11 ∷
   re 10 5 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q15 ∷
   rw 12 q28 ∷
   rw 11 q17 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q11 ∷
   re 11 5 (ℓ "乑") ∷
   re 11 1 (ℓ "乏丼临丼乏") ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q15 ∷
   rw 13 q28 ∷
   rw 12 q17 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q11 ∷
   re 12 5 (ℓ "乑") ∷
   rw 14 q18 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw⁻ 14 q1 ∷
   rw 13 q23 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (ℓ "乔") ∷
   rw 13 q24 ∷
   rw 12 q4 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q1 ∷
   rw 14 q25 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q6 ∷
   rw 6 q29 ∷
   rw 5 q30 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   rw 0 q31 ∷ []) Eq.refl
