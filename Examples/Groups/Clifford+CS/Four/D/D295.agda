{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D295 (W : Ws) where

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
  q2 = wE 20 W
  q3 : Eqn
  q3 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q4 : Eqn
  q4 = wE 49 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q7 : Eqn
  q7 = wE 606 W
  q8 : Eqn
  q8 = eqn (ℓ "丶业") (ℓ "业丶") (low₃-comm ((CS ↑)) (S))
  q9 : Eqn
  q9 = wE 607 W
  q10 : Eqn
  q10 = wE 103 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS12]: 173 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS12 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丶") ⟫ʷ ≈ ⟪ (ℓ "丶丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS12 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丶") (ℓ "丶丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q5 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q5 ∷
   re 28 5 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q2 ∷
   rw 28 q6 ∷
   rw 27 q4 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q5 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼临丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "丽") ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q5 ∷
   re 26 5 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q2 ∷
   rw 26 q6 ∷
   rw 25 q4 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q5 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q2 ∷
   rw 25 q6 ∷
   rw 24 q4 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q5 ∷
   re 24 5 (ℓ "中") ∷
   rw 22 q7 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q2 ∷
   rw 23 q6 ∷
   rw 22 q4 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q5 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q2 ∷
   rw 22 q6 ∷
   rw 21 q4 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q5 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q2 ∷
   rw 21 q6 ∷
   rw 20 q4 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q5 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q2 ∷
   rw 20 q6 ∷
   rw 19 q4 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q5 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q2 ∷
   rw 19 q6 ∷
   rw 18 q4 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q5 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q2 ∷
   rw 18 q6 ∷
   rw 17 q4 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q5 ∷
   re 17 5 (ℓ "中") ∷
   rw⁻ 15 q8 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q5 ∷
   re 15 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q2 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q5 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q2 ∷
   rw 14 q6 ∷
   rw 13 q4 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q5 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q2 ∷
   rw 13 q6 ∷
   rw 12 q4 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q5 ∷
   re 12 5 (ℓ "中") ∷
   rw⁻ 10 q8 ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q2 ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q5 ∷
   re 10 5 (ℓ "乑") ∷
   rw⁻ 8 q8 ∷
   re 7 1 (ℓ "乏丼临丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   rw 8 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   re 8 5 (ℓ "乑") ∷
   rw 6 q7 ∷
   rw 5 q9 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 2 q9 ∷
   rw 1 q10 ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 464 W
  q12 : Eqn
  q12 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q13 : Eqn
  q13 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q14 : Eqn
  q14 = wE 586 W
  q15 : Eqn
  q15 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q17 : Eqn
  q17 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q18 : Eqn
  q18 = wE 892 W
  q19 : Eqn
  q19 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q22 : Eqn
  q22 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q23 : Eqn
  q23 = wE 140 W
  q24 : Eqn
  q24 = wE 893 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = wE 7 W
  q28 : Eqn
  q28 = wE 894 W
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 583 W
  q31 : Eqn
  q31 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CX32]: 291 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CX32 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑乖") ⟫ʷ ≈ ⟪ (ℓ "乖丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CX32 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑乖") (ℓ "乖丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 29 q1 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q5 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q5 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q5 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q5 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q5 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q5 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q5 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q5 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q5 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q5 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q5 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q5 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q5 ∷
   rw 15 q11 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q5 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   rw 10 q11 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q5 ∷
   rw 8 q11 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q5 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q5 ∷
   rw 5 q12 ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q12 ∷
   rw 1 q13 ∷
   rw 0 q13 ∷
   rw 1 q14 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乑") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乑") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乓") ∷
   rw⁻ 7 q12 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 9 q12 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 11 q13 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 13 q13 ∷
   rw⁻ 14 q12 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 16 q13 ∷
   rw⁻ 17 q13 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 19 q13 ∷
   rw⁻ 20 q13 ∷
   rw⁻ 21 q13 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乓") ∷
   rw⁻ 23 q13 ∷
   rw⁻ 24 q13 ∷
   rw⁻ 25 q12 ∷
   rw⁻ 26 q13 ∷
   rw⁻ 27 q12 ∷
   rw⁻ 28 q12 ∷
   rw 29 q5 ∷
   rw 28 q16 ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q16 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   rw 22 q18 ∷
   rw 21 q17 ∷
   rw 20 q17 ∷
   rw 19 q17 ∷
   rw 18 q17 ∷
   rw 17 q17 ∷
   rw 16 q17 ∷
   rw 15 q19 ∷
   rw 14 q16 ∷
   rw 13 q17 ∷
   rw 12 q17 ∷
   rw 11 q17 ∷
   rw 10 q19 ∷
   rw 9 q16 ∷
   rw 8 q19 ∷
   rw 7 q16 ∷
   rw 6 q18 ∷
   rw 7 q20 ∷
   rw⁻ 6 q21 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q22 ∷
   rw 6 q23 ∷
   rw⁻ 5 q22 ∷
   re 6 3 (ℓ "乔") ∷
   rw 6 q24 ∷
   rw 5 q21 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q22 ∷
   rw 7 q25 ∷
   rw 8 q22 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q26 ∷
   rw 6 q20 ∷
   rw⁻ 5 q21 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q22 ∷
   rw 5 q23 ∷
   rw⁻ 4 q22 ∷
   re 5 3 (ℓ "乔") ∷
   rw 5 q24 ∷
   rw 4 q21 ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q22 ∷
   rw 6 q25 ∷
   rw 7 q22 ∷
   re 5 3 (ℓ "乑") ∷
   rw 6 q26 ∷
   rw 5 q20 ∷
   rw⁻ 4 q21 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q22 ∷
   rw 4 q27 ∷
   rw⁻ 3 q22 ∷
   re 4 3 (ℓ "丽") ∷
   rw 4 q28 ∷
   rw 3 q21 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q22 ∷
   rw 5 q29 ∷
   rw 6 q22 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q26 ∷
   rw 4 q20 ∷
   rw⁻ 3 q21 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q22 ∷
   rw 3 q23 ∷
   rw⁻ 2 q22 ∷
   re 3 3 (ℓ "乔") ∷
   rw 3 q24 ∷
   rw 2 q21 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q22 ∷
   rw 4 q25 ∷
   rw 5 q22 ∷
   re 3 3 (ℓ "乑") ∷
   rw 4 q26 ∷
   rw 3 q20 ∷
   rw⁻ 2 q21 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q22 ∷
   rw 2 q27 ∷
   rw⁻ 1 q22 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q28 ∷
   rw 1 q21 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q22 ∷
   rw 3 q29 ∷
   rw 4 q22 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q26 ∷
   rw 2 q20 ∷
   rw⁻ 1 q21 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q22 ∷
   rw 1 q27 ∷
   rw⁻ 0 q22 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q28 ∷
   rw 0 q21 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q22 ∷
   rw 2 q29 ∷
   rw 3 q22 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q26 ∷
   rw 30 q1 ∷
   rw 29 q12 ∷
   rw 28 q12 ∷
   rw 27 q13 ∷
   rw 26 q12 ∷
   rw 25 q13 ∷
   rw 24 q13 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 25 q5 ∷
   rw 22 q13 ∷
   rw 21 q13 ∷
   rw 20 q13 ∷
   rw 19 q13 ∷
   rw 18 q13 ∷
   rw 17 q13 ∷
   rw 16 q15 ∷
   rw 15 q12 ∷
   rw 14 q13 ∷
   rw 13 q13 ∷
   rw 12 q13 ∷
   rw 11 q15 ∷
   rw 10 q12 ∷
   rw 9 q15 ∷
   rw 8 q12 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q5 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q5 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q5 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   rw 2 q30 ∷
   rw⁻ 1 q13 ∷
   rw⁻ 2 q13 ∷
   rw⁻ 3 q12 ∷
   rw⁻ 4 q13 ∷
   rw⁻ 5 q12 ∷
   rw⁻ 6 q12 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乀") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q31 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q31 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q31 ∷
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
   re 23 3 (ℓ "乀") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "乑") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q5 ∷ []) Eq.refl
