{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D165 (W : Ws) where

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
  q3 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = wE 30 W
  q6 : Eqn
  q6 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 122 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 127 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 74 W
  q14 : Eqn
  q14 = wE 337 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q17 : Eqn
  q17 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q18 : Eqn
  q18 = wE 745 W
  q19 : Eqn
  q19 = wE 24 W
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W
  q22 : Eqn
  q22 = wE 142 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 TOFF302 X2]: 267 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF302-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乧丘") ⟫ʷ ≈ ⟪ (ℓ "丘乧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF302-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乧丘") (ℓ "丘乧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "並乨並") ∷
   re 31 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q8 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q3 ∷
   rw 37 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q12 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "丽") ∷
   rw 34 q13 ∷
   rw⁻ 33 q6 ∷
   rw 32 q13 ∷
   rw⁻ 31 q4 ∷
   rw⁻ 30 q3 ∷
   rw 31 q14 ∷
   re 31 8 (ℓ "乨") ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q7 ∷
   rw 29 q15 ∷
   rw⁻ 28 q7 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q7 ∷
   rw 28 q15 ∷
   rw⁻ 27 q7 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q7 ∷
   rw 27 q12 ∷
   rw⁻ 26 q7 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q7 ∷
   rw 26 q15 ∷
   rw⁻ 25 q7 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q7 ∷
   rw 25 q12 ∷
   rw⁻ 24 q7 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q7 ∷
   rw 24 q12 ∷
   rw⁻ 23 q7 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q16 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q7 ∷
   rw 22 q12 ∷
   rw⁻ 21 q7 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q7 ∷
   rw 21 q12 ∷
   rw⁻ 20 q7 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q7 ∷
   rw 20 q12 ∷
   rw⁻ 19 q7 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q7 ∷
   rw 19 q12 ∷
   rw⁻ 18 q7 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q7 ∷
   rw 18 q12 ∷
   rw⁻ 17 q7 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q7 ∷
   rw 17 q12 ∷
   rw⁻ 16 q7 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q17 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q7 ∷
   rw 15 q15 ∷
   rw⁻ 14 q7 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q7 ∷
   rw 14 q12 ∷
   rw⁻ 13 q7 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q7 ∷
   rw 13 q12 ∷
   rw⁻ 12 q7 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q7 ∷
   rw 12 q12 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q17 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q7 ∷
   rw 10 q15 ∷
   rw⁻ 9 q7 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q17 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q7 ∷
   rw 8 q15 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q16 ∷
   rw 5 q15 ∷
   rw 4 q15 ∷
   rw 3 q12 ∷
   rw 2 q15 ∷
   rw 1 q12 ∷
   rw 0 q12 ∷
   rw 1 q18 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q19 ∷
   rw 5 q6 ∷
   rw 6 q19 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q20 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q3 ∷
   rw 9 q21 ∷
   rw 2 q14 ∷
   re 2 8 (ℓ "乨") ∷
   re 1 3 (ℓ "乧") ∷
   rw 2 q2 ∷
   rw 3 q8 ∷
   rw 4 q8 ∷
   rw 5 q22 ∷
   rw 6 q8 ∷
   rw 7 q22 ∷
   rw 8 q22 ∷
   rw 9 q16 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q7 ∷
   rw 11 q22 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q17 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q7 ∷
   rw 13 q22 ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q17 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q7 ∷
   rw 15 q8 ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q7 ∷
   rw 16 q8 ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q7 ∷
   rw 17 q8 ∷
   rw 18 q7 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q7 ∷
   rw 18 q22 ∷
   rw 19 q7 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q17 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q7 ∷
   rw 20 q8 ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q7 ∷
   rw 21 q8 ∷
   rw 22 q7 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q7 ∷
   rw 22 q8 ∷
   rw 23 q7 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q7 ∷
   rw 23 q8 ∷
   rw 24 q7 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q7 ∷
   rw 24 q8 ∷
   rw 25 q7 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q7 ∷
   rw 25 q8 ∷
   rw 26 q7 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q16 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q7 ∷
   rw 27 q8 ∷
   rw 28 q7 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q7 ∷
   rw 28 q8 ∷
   rw 29 q7 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q7 ∷
   rw 29 q22 ∷
   rw 30 q7 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q7 ∷
   rw 30 q8 ∷
   rw 31 q7 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q7 ∷
   rw 31 q22 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q7 ∷
   rw 32 q22 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q10 ∷ []) Eq.refl
