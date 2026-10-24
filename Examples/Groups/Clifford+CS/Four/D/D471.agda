{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D471 (W : Ws) where

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
  q2 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = wE 1235 W
  q8 : Eqn
  q8 = wE 151 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [X0 CK03 X0]: 109 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CK03-X0 : ⟪ (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌丱丌") ⟫ʷ ≈ ⟪ (ℓ "丌丱丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CK03-X0 = derive (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌丱丌") (ℓ "丌丱丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏个乏") ∷
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
   re 1 3 (ℓ "丱") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丰") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乔") ∷
   rw 11 q8 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乔") ∷
   rw 13 q8 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乔") ∷
   rw 18 q8 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丰") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "丽") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乔") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "丽") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乔") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乔") ∷
   rw 32 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 1223 W
  q10 : Eqn
  q10 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q11 : Eqn
  q11 = eqn (ℓ "两之") (ℓ "之两") (low-comm (CK₀₁) (CZ))
  q12 : Eqn
  q12 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q15 : Eqn
  q15 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = wE 6 W
  q17 : Eqn
  q17 = wE 888 W
  q18 : Eqn
  q18 = wE 39 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = eqn (ℓ "丈之") (ℓ "之丈") (low₁-comm (S) ((CZ ↑)))
  q21 : Eqn
  q21 = wE 889 W
  q22 : Eqn
  q22 = wE 890 W
  q23 : Eqn
  q23 = wE 1224 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [CZ23]: 235 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CZ23 : ⟪ (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔之") ⟫ʷ ≈ ⟪ (ℓ "之丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CZ23 = derive (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔之") (ℓ "之丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔")
  (rw 29 q1 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   rw 0 q6 ∷
   rw 1 q9 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乔") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乔") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乔") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乐") ∷
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
   re 22 3 (ℓ "乐") ∷
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
   rw 24 q13 ∷
   rw⁻ 23 q14 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw⁻ 24 q15 ∷
   rw 23 q16 ∷
   rw⁻ 22 q15 ∷
   re 23 3 (ℓ "乓") ∷
   rw 23 q17 ∷
   rw 22 q14 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q15 ∷
   rw 24 q18 ∷
   rw 25 q15 ∷
   re 23 3 (ℓ "乐") ∷
   rw 24 q19 ∷
   rw 21 q12 ∷
   rw 20 q12 ∷
   rw 19 q12 ∷
   rw 18 q12 ∷
   rw 17 q12 ∷
   rw 16 q12 ∷
   rw 15 q20 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   rw 10 q20 ∷
   rw 9 q11 ∷
   rw 8 q20 ∷
   rw 7 q11 ∷
   rw 8 q13 ∷
   rw⁻ 7 q14 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q15 ∷
   rw 7 q16 ∷
   rw⁻ 6 q15 ∷
   re 7 3 (ℓ "乓") ∷
   rw 7 q17 ∷
   rw 6 q14 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 7 q15 ∷
   rw 8 q18 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q19 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q22 ∷
   rw 30 q1 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   rw 26 q5 ∷
   rw 25 q6 ∷
   rw 24 q6 ∷
   re 23 1 (ℓ "乏乃乏") ∷
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
   re 7 1 (ℓ "乏乃乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 2 q23 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丰") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乔") ∷
   rw 9 q8 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乔") ∷
   rw 11 q8 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乔") ∷
   rw 16 q8 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丰") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "乔") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乔") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乔") ∷
   rw 30 q3 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1225 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [CS03]: 105 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CS03 : ⟪ (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔中") ⟫ʷ ≈ ⟪ (ℓ "中丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CS03 = derive (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔中") (ℓ "中丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔")
  (rw 30 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 15 q4 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   rw 0 q6 ∷
   rw 1 q24 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丰") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乔") ∷
   rw 9 q8 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乔") ∷
   rw 11 q8 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乔") ∷
   rw 16 q8 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丽") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丰") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "乔") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乔") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乔") ∷
   rw 30 q3 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 279 W
  q26 : Eqn
  q26 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q27 : Eqn
  q27 = wE 280 W
  q28 : Eqn
  q28 = wE 65 W
  q29 : Eqn
  q29 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q30 : Eqn
  q30 = wE 48 W
  q31 : Eqn
  q31 = wE 7 W
  q32 : Eqn
  q32 = wE 74 W
  q33 : Eqn
  q33 = wE 606 W
  q34 : Eqn
  q34 = wE 27 W
  q35 : Eqn
  q35 = wE 30 W
  q36 : Eqn
  q36 = eqn (ℓ "丧业") (ℓ "业丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (S))
  q37 : Eqn
  q37 = wE 1226 W
  q38 : Eqn
  q38 = wE 95 W

-- pass [CS01 CS01 CK01 CS01 CK01 CK01 CX03 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX03 CS13 CS13 CK31 CS13 CK31 CK31] [CS02]: 129 steps
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CS02 : ⟪ (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丧") ⟫ʷ ≈ ⟪ (ℓ "丧丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔") ⟫ʷ
lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-CS02 = derive (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丧") (ℓ "丧丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔")
  (re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q25 ∷
   rw⁻ 29 q26 ∷
   rw 30 q27 ∷
   re 28 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q25 ∷
   rw⁻ 28 q26 ∷
   rw 29 q27 ∷
   re 27 3 (ℓ "丧") ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q28 ∷
   rw⁻ 27 q29 ∷
   rw 28 q30 ∷
   re 26 3 (ℓ "丧") ∷
   re 26 1 (ℓ "丼丠丼") ∷
   rw 25 q25 ∷
   rw⁻ 26 q26 ∷
   rw 27 q27 ∷
   re 25 3 (ℓ "丧") ∷
   re 25 1 (ℓ "丼丠丼") ∷
   rw 24 q28 ∷
   rw⁻ 25 q29 ∷
   rw 26 q30 ∷
   re 24 3 (ℓ "丧") ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q28 ∷
   rw⁻ 24 q29 ∷
   rw 25 q30 ∷
   re 23 3 (ℓ "丧") ∷
   rw 24 q13 ∷
   rw 23 q31 ∷
   re 22 1 (ℓ "乏个乏") ∷
   rw⁻ 24 q15 ∷
   rw 23 q32 ∷
   rw⁻ 22 q15 ∷
   re 23 3 (ℓ "乀") ∷
   rw 23 q33 ∷
   rw 22 q34 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 23 q15 ∷
   rw 24 q35 ∷
   rw 25 q15 ∷
   re 23 3 (ℓ "丰") ∷
   rw 24 q19 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q28 ∷
   rw⁻ 22 q29 ∷
   rw 23 q30 ∷
   re 21 3 (ℓ "丧") ∷
   re 21 1 (ℓ "丼丠丼") ∷
   rw 20 q28 ∷
   rw⁻ 21 q29 ∷
   rw 22 q30 ∷
   re 20 3 (ℓ "丧") ∷
   re 20 1 (ℓ "丼丠丼") ∷
   rw 19 q28 ∷
   rw⁻ 20 q29 ∷
   rw 21 q30 ∷
   re 19 3 (ℓ "丧") ∷
   re 19 1 (ℓ "丼丠丼") ∷
   rw 18 q28 ∷
   rw⁻ 19 q29 ∷
   rw 20 q30 ∷
   re 18 3 (ℓ "丧") ∷
   re 18 1 (ℓ "丼丠丼") ∷
   rw 17 q28 ∷
   rw⁻ 18 q29 ∷
   rw 19 q30 ∷
   re 17 3 (ℓ "丧") ∷
   re 17 1 (ℓ "丼丠丼") ∷
   rw 16 q28 ∷
   rw⁻ 17 q29 ∷
   rw 18 q30 ∷
   re 16 3 (ℓ "丧") ∷
   rw⁻ 15 q36 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 14 q25 ∷
   rw⁻ 15 q26 ∷
   rw 16 q27 ∷
   re 14 3 (ℓ "丧") ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 13 q28 ∷
   rw⁻ 14 q29 ∷
   rw 15 q30 ∷
   re 13 3 (ℓ "丧") ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 12 q28 ∷
   rw⁻ 13 q29 ∷
   rw 14 q30 ∷
   re 12 3 (ℓ "丧") ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 11 q28 ∷
   rw⁻ 12 q29 ∷
   rw 13 q30 ∷
   re 11 3 (ℓ "丧") ∷
   rw⁻ 10 q36 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 9 q25 ∷
   rw⁻ 10 q26 ∷
   rw 11 q27 ∷
   re 9 3 (ℓ "丧") ∷
   rw⁻ 8 q36 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q25 ∷
   rw⁻ 8 q26 ∷
   rw 9 q27 ∷
   re 7 3 (ℓ "丧") ∷
   rw 8 q13 ∷
   rw 7 q31 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw⁻ 8 q15 ∷
   rw 7 q32 ∷
   rw⁻ 6 q15 ∷
   re 7 3 (ℓ "乀") ∷
   rw 7 q33 ∷
   rw 6 q34 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q15 ∷
   rw 8 q35 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "丰") ∷
   rw 8 q19 ∷
   rw 5 q37 ∷
   rw 4 q37 ∷
   rw 3 q38 ∷
   rw 2 q37 ∷
   rw 1 q38 ∷
   rw 0 q38 ∷ []) Eq.refl
