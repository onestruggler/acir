{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D316 (W : Ws) where

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
  q5 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = wE 913 W
  q8 : Eqn
  q8 = wE 151 W

-- pass [CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [CS13]: 243 steps
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CS13 : ⟪ (ℓ "临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丽") ⟫ʷ ≈ ⟪ (ℓ "丽临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CS13 = derive (ℓ "临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丽") (ℓ "丽临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中")
  (rw 75 q1 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 76 q2 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q2 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q2 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q2 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q2 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q2 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q2 ∷
   rw 67 q3 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw 68 q2 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q2 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q2 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q2 ∷
   rw 62 q3 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 63 q2 ∷
   rw 60 q3 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 61 q2 ∷
   re 58 1 (ℓ "乏丹乏") ∷
   rw 60 q2 ∷
   rw 57 q3 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q2 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q2 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q2 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q2 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q2 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q2 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q2 ∷
   rw 38 q3 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q2 ∷
   rw 36 q3 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
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
   re 15 1 (ℓ "乏丹乏") ∷
   rw 17 q2 ∷
   rw 14 q4 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q4 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q6 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 6 q4 ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q4 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乀") ∷
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
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q8 ∷
   rw 36 q8 ∷
   rw 37 q8 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q8 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q8 ∷
   rw 50 q8 ∷
   rw 51 q8 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q8 ∷
   rw 54 q8 ∷
   rw 55 q8 ∷
   rw 56 q8 ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乑") ∷
   rw 58 q8 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乀") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乑") ∷
   rw 61 q8 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q8 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q8 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q2 ∷ []) Eq.refl
