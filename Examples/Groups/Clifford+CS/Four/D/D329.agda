{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D329 (W : Ws) where

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
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 464 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = wE 656 W
  q7 : Eqn
  q7 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q9 : Eqn
  q9 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q10 : Eqn
  q10 = wE 892 W
  q11 : Eqn
  q11 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q14 : Eqn
  q14 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 894 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 31 W
  q19 : Eqn
  q19 = wE 140 W
  q20 : Eqn
  q20 = wE 893 W
  q21 : Eqn
  q21 = wE 142 W
  q22 : Eqn
  q22 = wE 655 W
  q23 : Eqn
  q23 = wE 151 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [CX32]: 309 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CX32 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乖") ⟫ʷ ≈ ⟪ (ℓ "乖丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CX32 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乖") (ℓ "乖丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 31 q1 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q2 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q2 ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q2 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q2 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q4 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q6 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乓") ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q4 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q4 ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乓") ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q4 ∷
   rw 31 q2 ∷
   rw 30 q8 ∷
   rw 29 q8 ∷
   rw 28 q9 ∷
   rw 27 q8 ∷
   rw 26 q8 ∷
   rw 25 q8 ∷
   rw 24 q10 ∷
   rw 23 q8 ∷
   rw 22 q8 ∷
   rw 21 q8 ∷
   rw 20 q8 ∷
   rw 19 q8 ∷
   rw 18 q8 ∷
   rw 17 q8 ∷
   rw 16 q8 ∷
   rw 15 q8 ∷
   rw 14 q11 ∷
   rw 13 q9 ∷
   rw 12 q8 ∷
   rw 11 q8 ∷
   rw 10 q8 ∷
   rw 9 q8 ∷
   rw 8 q8 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 7 q12 ∷
   rw⁻ 6 q13 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q14 ∷
   rw 6 q15 ∷
   rw⁻ 5 q14 ∷
   re 6 3 (ℓ "丽") ∷
   rw 6 q16 ∷
   rw 5 q13 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q14 ∷
   rw 7 q17 ∷
   rw 8 q14 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q18 ∷
   rw 6 q12 ∷
   rw⁻ 5 q13 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q14 ∷
   rw 5 q15 ∷
   rw⁻ 4 q14 ∷
   re 5 3 (ℓ "丽") ∷
   rw 5 q16 ∷
   rw 4 q13 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q14 ∷
   rw 6 q17 ∷
   rw 7 q14 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q18 ∷
   rw 5 q12 ∷
   rw⁻ 4 q13 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q14 ∷
   rw 4 q19 ∷
   rw⁻ 3 q14 ∷
   re 4 3 (ℓ "乔") ∷
   rw 4 q20 ∷
   rw 3 q13 ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q14 ∷
   rw 5 q21 ∷
   rw 6 q14 ∷
   re 4 3 (ℓ "乑") ∷
   rw 5 q18 ∷
   rw 4 q12 ∷
   rw⁻ 3 q13 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q14 ∷
   rw 3 q15 ∷
   rw⁻ 2 q14 ∷
   re 3 3 (ℓ "丽") ∷
   rw 3 q16 ∷
   rw 2 q13 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   rw 5 q14 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q18 ∷
   rw 3 q12 ∷
   rw⁻ 2 q13 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q14 ∷
   rw 2 q15 ∷
   rw⁻ 1 q14 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q16 ∷
   rw 1 q13 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q14 ∷
   rw 3 q17 ∷
   rw 4 q14 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q18 ∷
   rw 2 q12 ∷
   rw⁻ 1 q13 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q14 ∷
   rw 1 q15 ∷
   rw⁻ 0 q14 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q16 ∷
   rw 0 q13 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q14 ∷
   rw 2 q17 ∷
   rw 3 q14 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q18 ∷
   rw 32 q1 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 27 q2 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q7 ∷
   rw 14 q5 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q2 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q2 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q2 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q2 ∷
   rw 2 q22 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q4 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乀") ∷
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
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q23 ∷
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
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乀") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乑") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q2 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 21 W
  q25 : Eqn
  q25 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q26 : Eqn
  q26 = wE 51 W
  q27 : Eqn
  q27 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q28 : Eqn
  q28 = wE 608 W
  q29 : Eqn
  q29 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q30 : Eqn
  q30 = wE 200 W
  q31 : Eqn
  q31 = wE 609 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [CSd12]: 207 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CSd12 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丷") ⟫ʷ ≈ ⟪ (ℓ "丷丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CSd12 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丷") (ℓ "丷丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q24 ∷
   rw 32 q25 ∷
   rw 31 q26 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q2 ∷
   re 31 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q24 ∷
   rw 31 q25 ∷
   rw 30 q26 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q2 ∷
   re 30 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q24 ∷
   rw 30 q27 ∷
   rw 29 q26 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q2 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q24 ∷
   rw 29 q25 ∷
   rw 28 q26 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q2 ∷
   re 28 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q24 ∷
   rw 28 q25 ∷
   rw 27 q26 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q2 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q24 ∷
   rw 27 q25 ∷
   rw 26 q26 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q2 ∷
   re 26 5 (ℓ "中") ∷
   rw 24 q28 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q24 ∷
   rw 25 q25 ∷
   rw 24 q26 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q2 ∷
   re 24 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q24 ∷
   rw 24 q25 ∷
   rw 23 q26 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q2 ∷
   re 23 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q24 ∷
   rw 23 q25 ∷
   rw 22 q26 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q2 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q24 ∷
   rw 22 q25 ∷
   rw 21 q26 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q2 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q24 ∷
   rw 21 q25 ∷
   rw 20 q26 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q2 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q24 ∷
   rw 20 q25 ∷
   rw 19 q26 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q2 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q24 ∷
   rw 19 q25 ∷
   rw 18 q26 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q2 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q24 ∷
   rw 18 q25 ∷
   rw 17 q26 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q2 ∷
   re 17 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "举") ∷
   rw 18 q24 ∷
   rw 17 q25 ∷
   rw 16 q26 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q2 ∷
   re 16 5 (ℓ "中") ∷
   rw⁻ 14 q29 ∷
   re 13 1 (ℓ "乏丼临丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q24 ∷
   rw 15 q27 ∷
   rw 14 q26 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q2 ∷
   re 14 5 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q24 ∷
   rw 14 q25 ∷
   rw 13 q26 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q2 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q24 ∷
   rw 13 q25 ∷
   rw 12 q26 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q2 ∷
   re 12 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q24 ∷
   rw 12 q25 ∷
   rw 11 q26 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q2 ∷
   re 11 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q24 ∷
   rw 11 q25 ∷
   rw 10 q26 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q2 ∷
   re 10 5 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q24 ∷
   rw 10 q25 ∷
   rw 9 q26 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q2 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw 10 q24 ∷
   rw 9 q25 ∷
   rw 8 q26 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q2 ∷
   re 8 5 (ℓ "中") ∷
   rw 6 q28 ∷
   rw 5 q30 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q30 ∷
   rw 1 q30 ∷
   rw 0 q30 ∷ []) Eq.refl
