{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D297 (W : Ws) where

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
  q8 = wE 897 W
  q9 : Eqn
  q9 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 X1]: 405 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乀中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中乀中中中中中中乑业中中中中中中中中中丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 117 q1 ∷
   rw 116 q2 ∷
   re 115 1 (ℓ "乏丧乏") ∷
   rw 117 q3 ∷
   re 114 1 (ℓ "乏丧乏") ∷
   rw 116 q3 ∷
   re 113 1 (ℓ "乏丧乏") ∷
   rw 115 q3 ∷
   re 112 1 (ℓ "乏丧乏") ∷
   rw 114 q3 ∷
   re 111 1 (ℓ "乏丧乏") ∷
   rw 113 q3 ∷
   re 110 1 (ℓ "乏丧乏") ∷
   rw 112 q3 ∷
   re 109 1 (ℓ "乏丧乏") ∷
   rw 111 q3 ∷
   re 108 1 (ℓ "乏丧乏") ∷
   rw 110 q3 ∷
   re 107 1 (ℓ "乏丧乏") ∷
   rw 109 q3 ∷
   rw 106 q4 ∷
   re 105 1 (ℓ "乏乄乏") ∷
   rw 107 q3 ∷
   re 104 1 (ℓ "乏丧乏") ∷
   rw 106 q3 ∷
   re 103 1 (ℓ "乏丧乏") ∷
   rw 105 q3 ∷
   re 102 1 (ℓ "乏丧乏") ∷
   rw 104 q3 ∷
   re 101 1 (ℓ "乏丧乏") ∷
   rw 103 q3 ∷
   re 100 1 (ℓ "乏丧乏") ∷
   rw 102 q3 ∷
   re 99 1 (ℓ "乏丧乏") ∷
   rw 101 q3 ∷
   re 98 1 (ℓ "乏丹乏") ∷
   rw 100 q3 ∷
   re 97 1 (ℓ "乏丧乏") ∷
   rw 99 q3 ∷
   re 96 1 (ℓ "乏丧乏") ∷
   rw 98 q3 ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q3 ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q3 ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw 95 q3 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q3 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q3 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 92 q3 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q3 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q3 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q3 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q3 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q3 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q3 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q3 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q3 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q3 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q3 ∷
   rw 79 q4 ∷
   re 78 1 (ℓ "乏乄乏") ∷
   rw 80 q3 ∷
   rw 77 q4 ∷
   rw 76 q4 ∷
   rw 75 q4 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q3 ∷
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
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q3 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q3 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q3 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q3 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q3 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q3 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q3 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q3 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q3 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q3 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q3 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q3 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q3 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q3 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q3 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q3 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q3 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q3 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q3 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q3 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 49 q3 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q5 ∷
   rw 39 q5 ∷
   rw 38 q5 ∷
   rw 37 q6 ∷
   rw 36 q7 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q5 ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
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
   rw 5 q7 ∷
   rw 4 q7 ∷
   rw 3 q5 ∷
   rw 2 q7 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q5 ∷
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
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
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
   rw 46 q9 ∷
   rw 47 q9 ∷
   rw 48 q9 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q9 ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乀") ∷
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
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "乑") ∷
   rw 77 q9 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   rw⁻ 87 q2 ∷
   rw⁻ 88 q5 ∷
   rw⁻ 89 q5 ∷
   rw⁻ 90 q7 ∷
   rw⁻ 91 q5 ∷
   rw⁻ 92 q7 ∷
   rw⁻ 93 q7 ∷
   rw 96 q1 ∷
   re 94 3 (ℓ "乀") ∷
   rw 97 q1 ∷
   re 95 3 (ℓ "乑") ∷
   rw 96 q9 ∷
   rw 99 q1 ∷
   re 97 3 (ℓ "乑") ∷
   rw 98 q9 ∷
   rw 101 q1 ∷
   re 99 3 (ℓ "中") ∷
   rw 102 q1 ∷
   re 100 3 (ℓ "中") ∷
   rw 103 q1 ∷
   re 101 3 (ℓ "中") ∷
   rw 104 q1 ∷
   re 102 3 (ℓ "乑") ∷
   rw 103 q9 ∷
   rw 106 q1 ∷
   re 104 3 (ℓ "中") ∷
   rw 107 q1 ∷
   re 105 3 (ℓ "中") ∷
   rw 108 q1 ∷
   re 106 3 (ℓ "中") ∷
   rw 109 q1 ∷
   re 107 3 (ℓ "中") ∷
   rw 110 q1 ∷
   re 108 3 (ℓ "中") ∷
   rw 111 q1 ∷
   re 109 3 (ℓ "中") ∷
   rw 112 q1 ∷
   re 110 3 (ℓ "乀") ∷
   rw 113 q1 ∷
   re 111 3 (ℓ "中") ∷
   rw 114 q1 ∷
   re 112 3 (ℓ "中") ∷
   rw 115 q1 ∷
   re 113 3 (ℓ "乑") ∷
   rw 116 q1 ∷
   re 114 3 (ℓ "中") ∷
   rw 117 q1 ∷
   re 115 3 (ℓ "乑") ∷
   rw 118 q1 ∷
   re 116 3 (ℓ "乑") ∷
   rw 117 q3 ∷ []) Eq.refl
