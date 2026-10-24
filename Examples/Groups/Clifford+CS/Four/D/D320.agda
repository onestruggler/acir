{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D320 (W : Ws) where

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
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = wE 942 W
  q9 : Eqn
  q9 = wE 151 W

-- pass [CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [X1 CKd13 X1]: 247 steps
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-CKd13-X1 : ⟪ (ℓ "临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丒乂丒") ⟫ʷ ≈ ⟪ (ℓ "丒乂丒临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-CKd13-X1 = derive (ℓ "临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中丒乂丒") (ℓ "丒乂丒临与临与丠丠丠临与丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业乀乑业乑业中中中乑业中中中中中中")
  (rw 77 q1 ∷
   rw 76 q2 ∷
   re 75 1 (ℓ "乏主乏") ∷
   rw 77 q3 ∷
   rw 74 q2 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q3 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q3 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q3 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q3 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q3 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q3 ∷
   rw 67 q4 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw 68 q3 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q3 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q3 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q3 ∷
   rw 62 q4 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 63 q3 ∷
   rw 60 q4 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 61 q3 ∷
   re 58 1 (ℓ "乏丹乏") ∷
   rw 60 q3 ∷
   rw 57 q4 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q3 ∷
   rw 55 q4 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   rw 52 q4 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q3 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q3 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q3 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q3 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   rw 38 q4 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q3 ∷
   rw 36 q4 ∷
   rw 35 q4 ∷
   rw 34 q4 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q3 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q3 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q3 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q3 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丧乏") ∷
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
   re 15 1 (ℓ "乏丹乏") ∷
   rw 17 q3 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q5 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q7 ∷
   rw 1 q6 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乂") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q7 ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q5 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乀") ∷
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
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q9 ∷
   rw 38 q9 ∷
   rw 39 q9 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q9 ∷
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
   rw 51 q1 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q9 ∷
   rw 52 q9 ∷
   rw 53 q9 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乑") ∷
   rw 55 q9 ∷
   rw 56 q9 ∷
   rw 57 q9 ∷
   rw 58 q9 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乑") ∷
   rw 60 q9 ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "乀") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q9 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乑") ∷
   rw 65 q9 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乑") ∷
   rw 70 q9 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q3 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q11 : Eqn
  q11 = wE 943 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 CK10 CS01 CS01 CKd10 X1]: 125 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-CS01-CS01-CKd10-X1 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临丠丠丵丒") ⟫ʷ ≈ ⟪ (ℓ "丒临丠丠丵丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-CS01-CS01-CKd10-X1 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临丠丠丵丒") (ℓ "丒临丠丠丵丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 37 q1 ∷
   rw 36 q2 ∷
   rw 35 q10 ∷
   rw 34 q5 ∷
   rw 33 q5 ∷
   rw 32 q7 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q3 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丧乏") ∷
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
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q3 ∷
   rw 14 q4 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q7 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q11 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q7 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 6 q5 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q7 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乀") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乑") ∷
   rw 20 q9 ∷
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
   re 30 3 (ℓ "乀") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乑") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q3 ∷ []) Eq.refl
