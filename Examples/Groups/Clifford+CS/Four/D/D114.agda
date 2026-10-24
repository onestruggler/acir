{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D114 (W : Ws) where

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
  q1 = wE 668 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CX21 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CX21-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乆丘") ⟫ʷ ≈ ⟪ (ℓ "丘乆丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CX21-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乆丘") (ℓ "丘乆丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = wE 669 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘") ⟫ʷ ≈ ⟪ (ℓ "丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘") (ℓ "丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q2 ∷ []) Eq.refl

private
  q3 : Eqn
  q3 = wE 670 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘") ⟫ʷ ≈ ⟪ (ℓ "丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-X2 = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘") (ℓ "丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q6 : Eqn
  q6 = wE 7 W
  q7 : Eqn
  q7 = wE 137 W
  q8 : Eqn
  q8 = wE 76 W
  q9 : Eqn
  q9 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = wE 140 W
  q11 : Eqn
  q11 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q12 : Eqn
  q12 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q13 : Eqn
  q13 = wE 671 W
  q14 : Eqn
  q14 = wE 29 W
  q15 : Eqn
  q15 = wE 139 W
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = wE 31 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CSd02 CKd20 CS02 CS02 X2]: 217 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-CKd20-CS02-CS02-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨久丧丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨久丧丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CSd02-CKd20-CS02-CS02-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丨久丧丧丘") (ℓ "丘丨久丧丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 35 q4 ∷
   rw⁻ 34 q5 ∷
   rw 33 q6 ∷
   rw 32 q6 ∷
   rw 31 q7 ∷
   rw 30 q8 ∷
   rw⁻ 29 q5 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q9 ∷
   rw 29 q10 ∷
   rw⁻ 28 q9 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q9 ∷
   rw 28 q10 ∷
   rw⁻ 27 q9 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q9 ∷
   rw 27 q6 ∷
   rw⁻ 26 q9 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q9 ∷
   rw 26 q10 ∷
   rw⁻ 25 q9 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q9 ∷
   rw 25 q6 ∷
   rw⁻ 24 q9 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q9 ∷
   rw 24 q6 ∷
   rw⁻ 23 q9 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q11 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q9 ∷
   rw 22 q6 ∷
   rw⁻ 21 q9 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q9 ∷
   rw 21 q6 ∷
   rw⁻ 20 q9 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q9 ∷
   rw 20 q6 ∷
   rw⁻ 19 q9 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q9 ∷
   rw 19 q6 ∷
   rw⁻ 18 q9 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q9 ∷
   rw 18 q6 ∷
   rw⁻ 17 q9 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q9 ∷
   rw 17 q6 ∷
   rw⁻ 16 q9 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q12 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q9 ∷
   rw 15 q10 ∷
   rw⁻ 14 q9 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q9 ∷
   rw 14 q6 ∷
   rw⁻ 13 q9 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q9 ∷
   rw 13 q6 ∷
   rw⁻ 12 q9 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q9 ∷
   rw 12 q6 ∷
   rw⁻ 11 q9 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q12 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q9 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q12 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q9 ∷
   rw 8 q10 ∷
   rw⁻ 7 q9 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q11 ∷
   rw 5 q10 ∷
   rw 4 q10 ∷
   rw 3 q6 ∷
   rw 2 q10 ∷
   rw 1 q6 ∷
   rw 0 q6 ∷
   rw 1 q13 ∷
   rw 0 q5 ∷
   rw 1 q14 ∷
   rw 2 q15 ∷
   rw 3 q16 ∷
   rw 4 q16 ∷
   rw 5 q5 ∷
   rw 6 q16 ∷
   rw 7 q16 ∷
   rw 8 q17 ∷
   rw 9 q16 ∷
   rw 10 q17 ∷
   rw 11 q17 ∷
   rw 12 q11 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q9 ∷
   rw 14 q17 ∷
   rw 15 q9 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q12 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q9 ∷
   rw 16 q17 ∷
   rw 17 q9 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q12 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q9 ∷
   rw 18 q16 ∷
   rw 19 q9 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q9 ∷
   rw 19 q16 ∷
   rw 20 q9 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q9 ∷
   rw 20 q16 ∷
   rw 21 q9 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q9 ∷
   rw 21 q17 ∷
   rw 22 q9 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q12 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q9 ∷
   rw 23 q16 ∷
   rw 24 q9 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q9 ∷
   rw 24 q16 ∷
   rw 25 q9 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q9 ∷
   rw 25 q16 ∷
   rw 26 q9 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q9 ∷
   rw 26 q16 ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q9 ∷
   rw 27 q16 ∷
   rw 28 q9 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q9 ∷
   rw 28 q16 ∷
   rw 29 q9 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q11 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q9 ∷
   rw 30 q16 ∷
   rw 31 q9 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q9 ∷
   rw 31 q16 ∷
   rw 32 q9 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q9 ∷
   rw 32 q17 ∷
   rw 33 q9 ∷
   re 31 3 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q9 ∷
   rw 33 q16 ∷
   rw 34 q9 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q9 ∷
   rw 34 q17 ∷
   rw 35 q9 ∷
   re 33 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q9 ∷
   rw 35 q17 ∷
   rw 36 q9 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q18 ∷ []) Eq.refl
