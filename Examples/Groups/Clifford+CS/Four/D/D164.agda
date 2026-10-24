{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D164 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = wE 140 W
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 743 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CK20 X2]: 211 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乄丘") ⟫ʷ ≈ ⟪ (ℓ "丘乄丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CK20-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乄丘") (ℓ "丘乄丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q4 ∷
   rw 29 q3 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q4 ∷
   rw 28 q3 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q4 ∷
   rw 26 q3 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q4 ∷
   rw 25 q5 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q4 ∷
   rw 24 q5 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q4 ∷
   rw 22 q5 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q4 ∷
   rw 21 q5 ∷
   rw⁻ 20 q4 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q4 ∷
   rw 20 q5 ∷
   rw⁻ 19 q4 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q4 ∷
   rw 19 q5 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q4 ∷
   rw 18 q5 ∷
   rw⁻ 17 q4 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q4 ∷
   rw 17 q5 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q7 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q4 ∷
   rw 15 q3 ∷
   rw⁻ 14 q4 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q4 ∷
   rw 14 q5 ∷
   rw⁻ 13 q4 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q4 ∷
   rw 13 q5 ∷
   rw⁻ 12 q4 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q4 ∷
   rw 12 q5 ∷
   rw⁻ 11 q4 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q7 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q4 ∷
   rw 10 q3 ∷
   rw⁻ 9 q4 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q7 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q4 ∷
   rw 8 q3 ∷
   rw⁻ 7 q4 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q6 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q5 ∷
   rw 2 q3 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q6 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q4 ∷
   rw 11 q9 ∷
   rw 12 q4 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q7 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q4 ∷
   rw 13 q9 ∷
   rw 14 q4 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q7 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q4 ∷
   rw 15 q10 ∷
   rw 16 q4 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q4 ∷
   rw 16 q10 ∷
   rw 17 q4 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q4 ∷
   rw 17 q10 ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q4 ∷
   rw 18 q9 ∷
   rw 19 q4 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q7 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q4 ∷
   rw 20 q10 ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q4 ∷
   rw 21 q10 ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q4 ∷
   rw 22 q10 ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q4 ∷
   rw 23 q10 ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q4 ∷
   rw 24 q10 ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q4 ∷
   rw 25 q10 ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q6 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q4 ∷
   rw 27 q10 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q4 ∷
   rw 28 q10 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q4 ∷
   rw 29 q9 ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q4 ∷
   rw 30 q10 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q4 ∷
   rw 31 q9 ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q4 ∷
   rw 32 q9 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 137 W
  q13 : Eqn
  q13 = wE 744 W
  q14 : Eqn
  q14 = wE 139 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CKd20 X2]: 211 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘久丘") ⟫ʷ ≈ ⟪ (ℓ "丘久丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CKd20-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘久丘") (ℓ "丘久丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   rw 30 q12 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q4 ∷
   rw 29 q3 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q4 ∷
   rw 28 q3 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q4 ∷
   rw 26 q3 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q4 ∷
   rw 25 q5 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q4 ∷
   rw 24 q5 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q4 ∷
   rw 22 q5 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q4 ∷
   rw 21 q5 ∷
   rw⁻ 20 q4 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q4 ∷
   rw 20 q5 ∷
   rw⁻ 19 q4 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q4 ∷
   rw 19 q5 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q4 ∷
   rw 18 q5 ∷
   rw⁻ 17 q4 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q4 ∷
   rw 17 q5 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q7 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q4 ∷
   rw 15 q3 ∷
   rw⁻ 14 q4 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q4 ∷
   rw 14 q5 ∷
   rw⁻ 13 q4 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q4 ∷
   rw 13 q5 ∷
   rw⁻ 12 q4 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q4 ∷
   rw 12 q5 ∷
   rw⁻ 11 q4 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q7 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q4 ∷
   rw 10 q3 ∷
   rw⁻ 9 q4 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q7 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q4 ∷
   rw 8 q3 ∷
   rw⁻ 7 q4 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q6 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q5 ∷
   rw 2 q3 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q13 ∷
   rw 0 q2 ∷
   rw 1 q14 ∷
   rw 2 q2 ∷
   rw 3 q10 ∷
   rw 4 q10 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q6 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q4 ∷
   rw 11 q9 ∷
   rw 12 q4 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q7 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q4 ∷
   rw 13 q9 ∷
   rw 14 q4 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q7 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q4 ∷
   rw 15 q10 ∷
   rw 16 q4 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q4 ∷
   rw 16 q10 ∷
   rw 17 q4 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q4 ∷
   rw 17 q10 ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q4 ∷
   rw 18 q9 ∷
   rw 19 q4 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q7 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q4 ∷
   rw 20 q10 ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q4 ∷
   rw 21 q10 ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q4 ∷
   rw 22 q10 ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q4 ∷
   rw 23 q10 ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q4 ∷
   rw 24 q10 ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q4 ∷
   rw 25 q10 ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q6 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q4 ∷
   rw 27 q10 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q4 ∷
   rw 28 q10 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q4 ∷
   rw 29 q9 ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q4 ∷
   rw 30 q10 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q4 ∷
   rw 31 q9 ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q4 ∷
   rw 32 q9 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q11 ∷ []) Eq.refl
