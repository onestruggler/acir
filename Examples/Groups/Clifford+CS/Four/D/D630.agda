{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD630 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D630 (W : Ws) (Sᴰ : SD630) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CSd02-CKd20-CS02-CS02-vs-X2-TOFF123-X2 : St 1498
  lem-pass-CSd02-CKd20-CS02-CS02-vs-X2-TOFF123-X2 = pickᴰ 0 Sᴰ
  lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-TOFF123-X2 : St 1499
  lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-TOFF123-X2 = pickᴰ 1 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 1601 W
  q9 : Eqn
  q9 = wE 29 W
  q10 : Eqn
  q10 = wE 139 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 142 W
  q13 : Eqn
  q13 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = sE 1499 lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-TOFF123-X2
  q16 : Eqn
  q16 = sE 1498 lem-pass-CSd02-CKd20-CS02-CS02-vs-X2-TOFF123-X2
  q17 : Eqn
  q17 = wE 137 W
  q18 : Eqn
  q18 = wE 76 W
  q19 : Eqn
  q19 = wE 1602 W

-- pass [X3 CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30 X3] [X2 TOFF123 X2]: 706 steps
lem-pass-X3-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-X3-vs-X2-TOFF123-X2 : ⟪ (ℓ "丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丞丘乢丘") ⟫ʷ ≈ ⟪ (ℓ "丘乢丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丞") ⟫ʷ
lem-pass-X3-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-X3-vs-X2-TOFF123-X2 = derive (ℓ "丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丞丘乢丘") (ℓ "丘乢丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丞")
  (rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "乔") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q5 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q4 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "乔") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q5 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q5 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   rw⁻ 23 q6 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q5 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q5 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q5 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q5 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q5 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q5 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   rw⁻ 16 q7 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q4 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "乔") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q5 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q5 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q5 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 11 q7 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw⁻ 12 q3 ∷
   rw 11 q4 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (ℓ "乔") ∷
   rw⁻ 9 q7 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw⁻ 10 q3 ∷
   rw 9 q4 ∷
   rw⁻ 8 q3 ∷
   re 9 3 (ℓ "乔") ∷
   rw⁻ 7 q6 ∷
   rw 6 q4 ∷
   rw 5 q4 ∷
   rw 4 q5 ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw⁻ 0 q2 ∷
   rw 1 q8 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q11 ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 5 q13 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw 8 q11 ∷
   rw 9 q11 ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw 12 q13 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q6 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q11 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q11 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q11 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   rw 24 q11 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q11 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   rw 26 q11 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   rw 27 q11 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   rw 28 q11 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   rw 29 q11 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q3 ∷
   rw 30 q11 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q11 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   rw 32 q11 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q3 ∷
   rw 33 q11 ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q3 ∷
   rw 34 q11 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q3 ∷
   rw 35 q11 ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q3 ∷
   rw 36 q11 ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q3 ∷
   rw 37 q11 ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q3 ∷
   rw 38 q11 ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q7 ∷
   rw 39 q7 ∷
   rw 40 q7 ∷
   re 42 1 (ℓ "乏乇乏") ∷
   rw 41 q3 ∷
   rw 42 q12 ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "乑") ∷
   rw 42 q7 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q3 ∷
   rw 44 q11 ∷
   rw 45 q3 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q3 ∷
   rw 45 q11 ∷
   rw 46 q3 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q3 ∷
   rw 46 q11 ∷
   rw 47 q3 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q3 ∷
   rw 47 q11 ∷
   rw 48 q3 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q3 ∷
   rw 48 q11 ∷
   rw 49 q3 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q3 ∷
   rw 49 q11 ∷
   rw 50 q3 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q3 ∷
   rw 50 q11 ∷
   rw 51 q3 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q3 ∷
   rw 51 q11 ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q3 ∷
   rw 52 q11 ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q7 ∷
   rw 53 q7 ∷
   rw 54 q7 ∷
   re 56 1 (ℓ "乏乇乏") ∷
   rw 55 q3 ∷
   rw 56 q12 ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "乑") ∷
   rw 56 q7 ∷
   rw 57 q7 ∷
   rw 58 q7 ∷
   rw 59 q7 ∷
   re 61 1 (ℓ "乏乇乏") ∷
   rw 60 q3 ∷
   rw 61 q12 ∷
   rw 62 q3 ∷
   re 60 3 (ℓ "乑") ∷
   rw 61 q7 ∷
   rw 62 q6 ∷
   re 64 1 (ℓ "乏乇乏") ∷
   rw 63 q3 ∷
   rw 64 q12 ∷
   rw 65 q3 ∷
   re 63 3 (ℓ "乑") ∷
   rw 64 q7 ∷
   re 66 1 (ℓ "乏乇乏") ∷
   rw 65 q3 ∷
   rw 66 q12 ∷
   rw 67 q3 ∷
   re 65 3 (ℓ "乑") ∷
   rw 66 q7 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q3 ∷
   rw 68 q11 ∷
   rw 69 q3 ∷
   re 67 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q3 ∷
   rw 69 q11 ∷
   rw 70 q3 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q3 ∷
   rw 70 q11 ∷
   rw 71 q3 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q3 ∷
   rw 71 q12 ∷
   rw 72 q3 ∷
   re 70 3 (ℓ "乑") ∷
   rw 71 q7 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q3 ∷
   rw 73 q11 ∷
   rw 74 q3 ∷
   re 72 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q3 ∷
   rw 74 q11 ∷
   rw 75 q3 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q3 ∷
   rw 75 q11 ∷
   rw 76 q3 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q3 ∷
   rw 76 q11 ∷
   rw 77 q3 ∷
   re 75 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q3 ∷
   rw 77 q11 ∷
   rw 78 q3 ∷
   re 76 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q3 ∷
   rw 78 q11 ∷
   rw 79 q3 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q14 ∷
   rw 4 q15 ∷
   rw 0 q16 ∷
   rw 81 q1 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q3 ∷
   rw 81 q5 ∷
   rw⁻ 80 q3 ∷
   re 81 3 (ℓ "丽") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q3 ∷
   rw 80 q5 ∷
   rw⁻ 79 q3 ∷
   re 80 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q3 ∷
   rw 79 q5 ∷
   rw⁻ 78 q3 ∷
   re 79 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q3 ∷
   rw 78 q5 ∷
   rw⁻ 77 q3 ∷
   re 78 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q3 ∷
   rw 77 q5 ∷
   rw⁻ 76 q3 ∷
   re 77 3 (ℓ "丽") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q3 ∷
   rw 76 q5 ∷
   rw⁻ 75 q3 ∷
   re 76 3 (ℓ "丽") ∷
   rw⁻ 74 q7 ∷
   re 73 1 (ℓ "乏乄乏") ∷
   rw⁻ 75 q3 ∷
   rw 74 q4 ∷
   rw⁻ 73 q3 ∷
   re 74 3 (ℓ "乔") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q3 ∷
   rw 73 q5 ∷
   rw⁻ 72 q3 ∷
   re 73 3 (ℓ "丽") ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q3 ∷
   rw 72 q5 ∷
   rw⁻ 71 q3 ∷
   re 72 3 (ℓ "丽") ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q3 ∷
   rw 71 q5 ∷
   rw⁻ 70 q3 ∷
   re 71 3 (ℓ "丽") ∷
   rw⁻ 69 q7 ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw⁻ 70 q3 ∷
   rw 69 q4 ∷
   rw⁻ 68 q3 ∷
   re 69 3 (ℓ "乔") ∷
   rw⁻ 67 q7 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q3 ∷
   rw 67 q4 ∷
   rw⁻ 66 q3 ∷
   re 67 3 (ℓ "乔") ∷
   rw⁻ 65 q6 ∷
   rw⁻ 64 q7 ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw⁻ 65 q3 ∷
   rw 64 q4 ∷
   rw⁻ 63 q3 ∷
   re 64 3 (ℓ "乔") ∷
   rw⁻ 62 q7 ∷
   rw⁻ 61 q7 ∷
   rw⁻ 60 q7 ∷
   rw⁻ 59 q7 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw⁻ 60 q3 ∷
   rw 59 q4 ∷
   rw⁻ 58 q3 ∷
   re 59 3 (ℓ "乔") ∷
   rw⁻ 57 q7 ∷
   rw⁻ 56 q7 ∷
   rw⁻ 55 q7 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q3 ∷
   rw 55 q5 ∷
   rw⁻ 54 q3 ∷
   re 55 3 (ℓ "丽") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q3 ∷
   rw 54 q5 ∷
   rw⁻ 53 q3 ∷
   re 54 3 (ℓ "丽") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q3 ∷
   rw 53 q5 ∷
   rw⁻ 52 q3 ∷
   re 53 3 (ℓ "丽") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q3 ∷
   rw 52 q5 ∷
   rw⁻ 51 q3 ∷
   re 52 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q3 ∷
   rw 51 q5 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q3 ∷
   rw 50 q5 ∷
   rw⁻ 49 q3 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q3 ∷
   rw 49 q5 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q3 ∷
   rw 48 q5 ∷
   rw⁻ 47 q3 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q3 ∷
   rw 47 q5 ∷
   rw⁻ 46 q3 ∷
   re 47 3 (ℓ "丽") ∷
   rw⁻ 45 q7 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw⁻ 46 q3 ∷
   rw 45 q4 ∷
   rw⁻ 44 q3 ∷
   re 45 3 (ℓ "乔") ∷
   rw⁻ 43 q7 ∷
   rw⁻ 42 q7 ∷
   rw⁻ 41 q7 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q3 ∷
   rw 41 q5 ∷
   rw⁻ 40 q3 ∷
   re 41 3 (ℓ "丽") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q3 ∷
   rw 40 q5 ∷
   rw⁻ 39 q3 ∷
   re 40 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q3 ∷
   rw 39 q5 ∷
   rw⁻ 38 q3 ∷
   re 39 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q3 ∷
   rw 38 q5 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q3 ∷
   rw 37 q5 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (ℓ "丽") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q5 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q5 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "丽") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q5 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q5 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q5 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q5 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q5 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q5 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q5 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q5 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q5 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q5 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q5 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q6 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw⁻ 15 q13 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw⁻ 10 q13 ∷
   rw 9 q4 ∷
   rw⁻ 8 q13 ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q5 ∷
   rw 4 q17 ∷
   rw 3 q18 ∷
   rw 4 q19 ∷
   rw 3 q2 ∷
   rw 4 q11 ∷
   rw 5 q11 ∷
   rw 6 q12 ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q12 ∷
   rw 10 q6 ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q3 ∷
   rw 12 q12 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "乑") ∷
   rw 12 q7 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q3 ∷
   rw 14 q12 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q7 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   rw 16 q11 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw 17 q11 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   rw 18 q11 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q3 ∷
   rw 19 q12 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "乑") ∷
   rw 19 q7 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q11 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q11 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q11 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   rw 24 q11 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q11 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   rw 26 q11 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q6 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   rw 28 q11 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   rw 29 q11 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   rw 30 q12 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "乑") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q11 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q3 ∷
   rw 32 q12 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "乑") ∷
   re 33 1 (ℓ "乏乇乏") ∷
   rw 32 q3 ∷
   rw 33 q12 ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "乑") ∷
   rw 33 q2 ∷
   rw 34 q14 ∷ []) Eq.refl
