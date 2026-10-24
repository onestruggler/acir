{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D092 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 31 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 359 W
  q6 : Eqn
  q6 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q7 : Eqn
  q7 = wE 361 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 629 W
  q13 : Eqn
  q13 = wE 631 W
  q14 : Eqn
  q14 = wE 497 W
  q15 : Eqn
  q15 = wE 632 W
  q16 : Eqn
  q16 = wE 496 W

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [X2 CK21 X2] part3: 200 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CK21-X2-part3 : ⟪ (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中丘乏並丶乏並乇丘中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CK21-X2-part3 = derive (ℓ "乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中丘乏並丶乏並乇丘中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中") (ℓ "丘乇丘乄且乄且丧丧丧乄且丧丧丧丧丧丧乌中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乌乑业乑业中中中乑业中中中中中中")
  (rw 22 q1 ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q3 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "乔") ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q8 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q9 ∷
   rw⁻ 23 q10 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q2 ∷
   rw 23 q11 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q12 ∷
   rw 22 q10 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q3 ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q2 ∷
   rw 20 q11 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q12 ∷
   rw 19 q10 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q3 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "乔") ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q8 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q9 ∷
   rw⁻ 22 q10 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q2 ∷
   rw 22 q11 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q12 ∷
   rw 21 q10 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q3 ∷
   rw 20 q9 ∷
   rw⁻ 19 q10 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q2 ∷
   rw 19 q11 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q12 ∷
   rw 18 q10 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q3 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "乔") ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   rw 20 q7 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q8 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q9 ∷
   rw⁻ 21 q10 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q2 ∷
   rw 21 q11 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q12 ∷
   rw 20 q10 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q3 ∷
   rw 19 q9 ∷
   rw⁻ 18 q10 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q2 ∷
   rw 18 q11 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q12 ∷
   rw 17 q10 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q2 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q3 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "乔") ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q7 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q8 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q2 ∷
   rw 20 q11 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q12 ∷
   rw 19 q10 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q3 ∷
   rw 18 q9 ∷
   rw⁻ 17 q10 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q2 ∷
   rw 17 q11 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q12 ∷
   rw 16 q10 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q2 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q3 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "乔") ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q7 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q8 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q9 ∷
   rw⁻ 19 q10 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q2 ∷
   rw 19 q11 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q12 ∷
   rw 18 q10 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q3 ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   rw 13 q14 ∷
   rw 12 q14 ∷
   rw 11 q14 ∷
   rw 10 q14 ∷
   rw 9 q14 ∷
   rw 8 q15 ∷
   rw 7 q16 ∷
   rw 6 q14 ∷
   rw 5 q14 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 2 q16 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷ []) Eq.refl
