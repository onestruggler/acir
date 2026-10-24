{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D355 (W : Ws) where

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
  q1 = wE 31 W
  q2 : Eqn
  q2 = wE 673 W
  q3 : Eqn
  q3 = wE 488 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 505 W
  q10 : Eqn
  q10 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q11 : Eqn
  q11 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q12 : Eqn
  q12 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q13 : Eqn
  q13 = wE 464 W
  q14 : Eqn
  q14 = wE 506 W
  q15 : Eqn
  q15 = wE 151 W

-- Bar(SSKSKK;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part4: 179 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧乄丧乄乄乌丘乆丘乏乄乏並並业乑业中中中乑业中中中中中中乌中中乑中乑乑临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧乄丧乄乄乌丘乆丘乏乄乏並並业乑业中中中乑业中中中中中中乌中中乑中乑乑临与临与丠丠丠临与丠丠丠丠丠丠") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (re 72 3 (ℓ "乑") ∷
   rw 73 q1 ∷
   rw 68 q2 ∷
   rw 62 q3 ∷
   rw 109 q4 ∷
   rw 108 q5 ∷
   rw 107 q5 ∷
   rw 106 q5 ∷
   rw 105 q5 ∷
   rw 104 q5 ∷
   rw 103 q5 ∷
   rw 102 q6 ∷
   rw 101 q7 ∷
   rw 100 q5 ∷
   rw 99 q5 ∷
   rw 98 q5 ∷
   rw 97 q6 ∷
   rw 96 q7 ∷
   rw 95 q6 ∷
   rw 94 q7 ∷
   re 93 1 (ℓ "乏乄乏") ∷
   rw 95 q8 ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw 94 q8 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q8 ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw 92 q8 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q8 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q8 ∷
   rw 89 q9 ∷
   rw⁻ 88 q7 ∷
   rw⁻ 89 q6 ∷
   rw⁻ 90 q7 ∷
   rw⁻ 91 q6 ∷
   rw⁻ 92 q5 ∷
   rw⁻ 93 q5 ∷
   rw⁻ 94 q5 ∷
   rw⁻ 95 q7 ∷
   rw⁻ 96 q6 ∷
   rw⁻ 97 q5 ∷
   rw⁻ 98 q5 ∷
   rw⁻ 99 q5 ∷
   rw⁻ 100 q5 ∷
   rw⁻ 101 q5 ∷
   rw⁻ 102 q5 ∷
   rw 105 q4 ∷
   re 103 3 (ℓ "中") ∷
   rw 106 q4 ∷
   re 104 3 (ℓ "中") ∷
   rw 107 q4 ∷
   re 105 3 (ℓ "乑") ∷
   rw 108 q4 ∷
   re 106 3 (ℓ "中") ∷
   rw 109 q4 ∷
   re 107 3 (ℓ "乑") ∷
   rw 110 q4 ∷
   re 108 3 (ℓ "乑") ∷
   rw 109 q8 ∷
   rw⁻ 87 q10 ∷
   rw⁻ 88 q11 ∷
   rw⁻ 89 q10 ∷
   rw⁻ 90 q11 ∷
   rw⁻ 91 q12 ∷
   rw⁻ 92 q12 ∷
   rw⁻ 93 q12 ∷
   rw⁻ 94 q10 ∷
   rw⁻ 95 q11 ∷
   rw⁻ 96 q12 ∷
   rw⁻ 97 q12 ∷
   rw⁻ 98 q12 ∷
   rw⁻ 99 q12 ∷
   rw⁻ 100 q12 ∷
   rw⁻ 101 q12 ∷
   rw 102 q4 ∷
   rw 101 q5 ∷
   rw 100 q5 ∷
   rw 99 q5 ∷
   rw 98 q5 ∷
   rw 97 q5 ∷
   rw 96 q5 ∷
   rw 95 q6 ∷
   rw 94 q7 ∷
   rw 93 q5 ∷
   rw 92 q5 ∷
   rw 91 q5 ∷
   rw 90 q6 ∷
   rw 89 q7 ∷
   rw 88 q6 ∷
   rw 87 q7 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q8 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q8 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q8 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q8 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q8 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q8 ∷
   rw 80 q13 ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw 81 q8 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q8 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q8 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q8 ∷
   rw 75 q13 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw 76 q8 ∷
   rw 73 q13 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 74 q8 ∷
   rw 73 q14 ∷
   rw⁻ 72 q7 ∷
   rw⁻ 73 q6 ∷
   rw⁻ 74 q7 ∷
   rw⁻ 75 q6 ∷
   rw⁻ 76 q5 ∷
   rw⁻ 77 q5 ∷
   rw⁻ 78 q5 ∷
   rw⁻ 79 q7 ∷
   rw⁻ 80 q6 ∷
   rw⁻ 81 q5 ∷
   rw⁻ 82 q5 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q5 ∷
   rw⁻ 85 q5 ∷
   rw⁻ 86 q5 ∷
   rw 89 q4 ∷
   re 87 3 (ℓ "乑") ∷
   rw 88 q15 ∷
   rw 91 q4 ∷
   re 89 3 (ℓ "乑") ∷
   rw 90 q15 ∷
   rw 93 q4 ∷
   re 91 3 (ℓ "中") ∷
   rw 94 q4 ∷
   re 92 3 (ℓ "中") ∷
   rw 95 q4 ∷
   re 93 3 (ℓ "中") ∷
   rw 96 q4 ∷
   re 94 3 (ℓ "乑") ∷
   rw 95 q15 ∷
   rw 98 q4 ∷
   re 96 3 (ℓ "中") ∷
   rw 99 q4 ∷
   re 97 3 (ℓ "中") ∷
   rw 100 q4 ∷
   re 98 3 (ℓ "中") ∷
   rw 101 q4 ∷
   re 99 3 (ℓ "中") ∷
   rw 102 q4 ∷
   re 100 3 (ℓ "中") ∷
   rw 103 q4 ∷
   re 101 3 (ℓ "中") ∷
   rw 102 q8 ∷
   rw⁻ 71 q10 ∷
   rw⁻ 72 q11 ∷
   rw⁻ 73 q10 ∷
   rw⁻ 74 q11 ∷
   rw⁻ 75 q12 ∷
   rw⁻ 76 q12 ∷
   rw⁻ 77 q12 ∷
   rw⁻ 78 q10 ∷
   rw⁻ 79 q11 ∷
   rw⁻ 80 q12 ∷
   rw⁻ 81 q12 ∷
   rw⁻ 82 q12 ∷
   rw⁻ 83 q12 ∷
   rw⁻ 84 q12 ∷
   rw⁻ 85 q12 ∷
   rw 65 q9 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q18 : Eqn
  q18 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 7 W
  q22 : Eqn
  q22 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q23 : Eqn
  q23 = wE 970 W
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 142 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CX23 X2]: 211 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX23-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乌丘") ⟫ʷ ≈ ⟪ (ℓ "丘乌丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX23-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乌丘") (ℓ "丘乌丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q16 ∷
   rw⁻ 31 q17 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 29 q17 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q19 ∷
   rw 29 q20 ∷
   rw⁻ 28 q19 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q19 ∷
   rw 28 q20 ∷
   rw⁻ 27 q19 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q19 ∷
   rw 27 q21 ∷
   rw⁻ 26 q19 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q19 ∷
   rw 26 q20 ∷
   rw⁻ 25 q19 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q19 ∷
   rw 25 q21 ∷
   rw⁻ 24 q19 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q19 ∷
   rw 24 q21 ∷
   rw⁻ 23 q19 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q18 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q19 ∷
   rw 22 q21 ∷
   rw⁻ 21 q19 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q19 ∷
   rw 21 q21 ∷
   rw⁻ 20 q19 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q19 ∷
   rw 20 q21 ∷
   rw⁻ 19 q19 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q19 ∷
   rw 19 q21 ∷
   rw⁻ 18 q19 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q19 ∷
   rw 18 q21 ∷
   rw⁻ 17 q19 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q19 ∷
   rw 17 q21 ∷
   rw⁻ 16 q19 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q22 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q19 ∷
   rw 15 q20 ∷
   rw⁻ 14 q19 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q19 ∷
   rw 14 q21 ∷
   rw⁻ 13 q19 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q19 ∷
   rw 13 q21 ∷
   rw⁻ 12 q19 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q19 ∷
   rw 12 q21 ∷
   rw⁻ 11 q19 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q22 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q19 ∷
   rw 10 q20 ∷
   rw⁻ 9 q19 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q22 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q19 ∷
   rw 8 q20 ∷
   rw⁻ 7 q19 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q18 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 1 q23 ∷
   rw 0 q17 ∷
   rw 1 q18 ∷
   rw 2 q17 ∷
   rw 3 q24 ∷
   rw 4 q24 ∷
   rw 5 q25 ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q25 ∷
   rw 9 q18 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q19 ∷
   rw 11 q25 ∷
   rw 12 q19 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q22 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q19 ∷
   rw 13 q25 ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q22 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q19 ∷
   rw 15 q24 ∷
   rw 16 q19 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q19 ∷
   rw 16 q24 ∷
   rw 17 q19 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q19 ∷
   rw 17 q24 ∷
   rw 18 q19 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q19 ∷
   rw 18 q25 ∷
   rw 19 q19 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q22 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q19 ∷
   rw 20 q24 ∷
   rw 21 q19 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q19 ∷
   rw 21 q24 ∷
   rw 22 q19 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q19 ∷
   rw 22 q24 ∷
   rw 23 q19 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q19 ∷
   rw 23 q24 ∷
   rw 24 q19 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q19 ∷
   rw 24 q24 ∷
   rw 25 q19 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q19 ∷
   rw 25 q24 ∷
   rw 26 q19 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q18 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q19 ∷
   rw 27 q24 ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q19 ∷
   rw 28 q24 ∷
   rw 29 q19 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q19 ∷
   rw 29 q25 ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q19 ∷
   rw 30 q24 ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q19 ∷
   rw 31 q25 ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q19 ∷
   rw 32 q25 ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q1 ∷ []) Eq.refl
