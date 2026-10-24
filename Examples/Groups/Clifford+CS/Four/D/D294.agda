{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D294 (W : Ws) where

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
  q2 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = wE 887 W
  q8 : Eqn
  q8 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CK13 X1]: 109 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK13-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒乁丒") ⟫ʷ ≈ ⟪ (ℓ "丒乁丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK13-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒乁丒") (ℓ "丒乁丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏为乏") ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乁") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乀") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q8 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q8 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q8 ∷
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
   re 28 3 (ℓ "乑") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 586 W
  q10 : Eqn
  q10 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "临之") (ℓ "之临") (low-comm (CK₁₀) (CZ))
  q12 : Eqn
  q12 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q13 : Eqn
  q13 = wE 888 W
  q14 : Eqn
  q14 = eqn (ℓ "与之") (ℓ "之与") (low-comm ((S ↑)) (CZ))
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q17 : Eqn
  q17 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 140 W
  q19 : Eqn
  q19 = wE 889 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = wE 7 W
  q23 : Eqn
  q23 = wE 890 W
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 583 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CZ23]: 291 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CZ23 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑之") ⟫ʷ ≈ ⟪ (ℓ "之丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CZ23 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑之") (ℓ "之丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 29 q1 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   rw 0 q6 ∷
   rw 1 q9 ∷
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
   rw⁻ 7 q5 ∷
   rw⁻ 8 q10 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q10 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q10 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 21 q6 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乓") ∷
   rw⁻ 23 q6 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q5 ∷
   rw 29 q3 ∷
   rw 28 q11 ∷
   rw 27 q11 ∷
   rw 26 q12 ∷
   rw 25 q11 ∷
   rw 24 q12 ∷
   rw 23 q12 ∷
   rw 22 q13 ∷
   rw 21 q12 ∷
   rw 20 q12 ∷
   rw 19 q12 ∷
   rw 18 q12 ∷
   rw 17 q12 ∷
   rw 16 q12 ∷
   rw 15 q14 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   rw 10 q14 ∷
   rw 9 q11 ∷
   rw 8 q14 ∷
   rw 7 q11 ∷
   rw 6 q13 ∷
   rw 7 q15 ∷
   rw⁻ 6 q16 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q17 ∷
   rw 6 q18 ∷
   rw⁻ 5 q17 ∷
   re 6 3 (ℓ "乔") ∷
   rw 6 q19 ∷
   rw 5 q16 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q17 ∷
   rw 7 q20 ∷
   rw 8 q17 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q21 ∷
   rw 6 q15 ∷
   rw⁻ 5 q16 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q17 ∷
   rw 5 q18 ∷
   rw⁻ 4 q17 ∷
   re 5 3 (ℓ "乔") ∷
   rw 5 q19 ∷
   rw 4 q16 ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q17 ∷
   rw 6 q20 ∷
   rw 7 q17 ∷
   re 5 3 (ℓ "乑") ∷
   rw 6 q21 ∷
   rw 5 q15 ∷
   rw⁻ 4 q16 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q17 ∷
   rw 4 q22 ∷
   rw⁻ 3 q17 ∷
   re 4 3 (ℓ "丽") ∷
   rw 4 q23 ∷
   rw 3 q16 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q17 ∷
   rw 5 q24 ∷
   rw 6 q17 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q21 ∷
   rw 4 q15 ∷
   rw⁻ 3 q16 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q17 ∷
   rw 3 q18 ∷
   rw⁻ 2 q17 ∷
   re 3 3 (ℓ "乔") ∷
   rw 3 q19 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q17 ∷
   rw 4 q20 ∷
   rw 5 q17 ∷
   re 3 3 (ℓ "乑") ∷
   rw 4 q21 ∷
   rw 3 q15 ∷
   rw⁻ 2 q16 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q17 ∷
   rw 2 q22 ∷
   rw⁻ 1 q17 ∷
   re 2 3 (ℓ "丽") ∷
   rw 2 q23 ∷
   rw 1 q16 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q17 ∷
   rw 3 q24 ∷
   rw 4 q17 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q21 ∷
   rw 2 q15 ∷
   rw⁻ 1 q16 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q17 ∷
   rw 1 q22 ∷
   rw⁻ 0 q17 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q23 ∷
   rw 0 q16 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q17 ∷
   rw 2 q24 ∷
   rw 3 q17 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q21 ∷
   rw 30 q1 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   rw 26 q5 ∷
   rw 25 q6 ∷
   rw 24 q6 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 25 q3 ∷
   rw 22 q6 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   rw 16 q10 ∷
   rw 15 q5 ∷
   rw 14 q6 ∷
   rw 13 q6 ∷
   rw 12 q6 ∷
   rw 11 q10 ∷
   rw 10 q5 ∷
   rw 9 q10 ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q3 ∷
   rw 2 q25 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乀") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q8 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q8 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q8 ∷
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
   rw 30 q3 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 891 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS13]: 105 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS13 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丽") ⟫ʷ ≈ ⟪ (ℓ "丽丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS13 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丽") (ℓ "丽丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 30 q1 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   rw 0 q6 ∷
   rw 1 q26 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乀") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q8 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q8 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q8 ∷
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
   rw 30 q3 ∷ []) Eq.refl
