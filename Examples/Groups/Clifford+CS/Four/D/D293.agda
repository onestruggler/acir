{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D293 (W : Ws) where

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
  q1 = wE 7 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 885 W
  q6 : Eqn
  q6 = wE 142 W
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 36 W
  q11 : Eqn
  q11 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 37 W
  q13 : Eqn
  q13 = wE 883 W
  q14 : Eqn
  q14 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q15 : Eqn
  q15 = wE 617 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part4: 195 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part4 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中乏丧並乏丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並乀中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part4 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中乏丧並乏丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並乀中中乑中乑乑") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 85 q1 ∷
   rw⁻ 84 q2 ∷
   re 85 3 (ℓ "丽") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q2 ∷
   rw 84 q1 ∷
   rw⁻ 83 q2 ∷
   re 84 3 (ℓ "丽") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q2 ∷
   rw 83 q1 ∷
   rw⁻ 82 q2 ∷
   re 83 3 (ℓ "丽") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q2 ∷
   rw 82 q1 ∷
   rw⁻ 81 q2 ∷
   re 82 3 (ℓ "丽") ∷
   rw⁻ 80 q3 ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw⁻ 81 q2 ∷
   rw 80 q4 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (ℓ "乔") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q2 ∷
   rw 79 q1 ∷
   rw⁻ 78 q2 ∷
   re 79 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q2 ∷
   rw 78 q1 ∷
   rw⁻ 77 q2 ∷
   re 78 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q2 ∷
   rw 77 q1 ∷
   rw⁻ 76 q2 ∷
   re 77 3 (ℓ "丽") ∷
   rw⁻ 75 q3 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw⁻ 76 q2 ∷
   rw 75 q4 ∷
   rw⁻ 74 q2 ∷
   re 75 3 (ℓ "乔") ∷
   rw⁻ 73 q3 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw⁻ 74 q2 ∷
   rw 73 q4 ∷
   rw⁻ 72 q2 ∷
   re 73 3 (ℓ "乔") ∷
   rw 73 q5 ∷
   rw 72 q6 ∷
   rw 73 q7 ∷
   rw 74 q6 ∷
   rw 75 q7 ∷
   rw 76 q8 ∷
   rw 77 q8 ∷
   rw 78 q8 ∷
   rw 79 q6 ∷
   rw 80 q7 ∷
   rw 81 q8 ∷
   rw 82 q8 ∷
   rw 83 q8 ∷
   rw 84 q8 ∷
   rw 85 q8 ∷
   rw 86 q8 ∷
   re 88 1 (ℓ "乏乇乏") ∷
   rw 87 q2 ∷
   rw 88 q6 ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乑") ∷
   rw 88 q3 ∷
   re 90 1 (ℓ "乏乇乏") ∷
   rw 89 q2 ∷
   rw 90 q6 ∷
   rw 91 q2 ∷
   re 89 3 (ℓ "乑") ∷
   rw 90 q3 ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q2 ∷
   rw 92 q8 ∷
   rw 93 q2 ∷
   re 91 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q2 ∷
   rw 93 q8 ∷
   rw 94 q2 ∷
   re 92 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏丶乏") ∷
   rw 93 q2 ∷
   rw 94 q8 ∷
   rw 95 q2 ∷
   re 93 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏乇乏") ∷
   rw 94 q2 ∷
   rw 95 q6 ∷
   rw 96 q2 ∷
   re 94 3 (ℓ "乑") ∷
   rw 95 q3 ∷
   re 97 1 (ℓ "乏丶乏") ∷
   rw 96 q2 ∷
   rw 97 q8 ∷
   rw 98 q2 ∷
   re 96 3 (ℓ "中") ∷
   re 98 1 (ℓ "乏丶乏") ∷
   rw 97 q2 ∷
   rw 98 q8 ∷
   rw 99 q2 ∷
   re 97 3 (ℓ "中") ∷
   re 99 1 (ℓ "乏丶乏") ∷
   rw 98 q2 ∷
   rw 99 q8 ∷
   rw 100 q2 ∷
   re 98 3 (ℓ "中") ∷
   re 100 1 (ℓ "乏丶乏") ∷
   rw 99 q2 ∷
   rw 100 q8 ∷
   rw 101 q2 ∷
   re 99 3 (ℓ "中") ∷
   re 101 1 (ℓ "乏丶乏") ∷
   rw 100 q2 ∷
   rw 101 q8 ∷
   rw 102 q2 ∷
   re 100 3 (ℓ "中") ∷
   re 102 1 (ℓ "乏丶乏") ∷
   rw 101 q2 ∷
   rw 102 q8 ∷
   rw 103 q2 ∷
   re 101 3 (ℓ "中") ∷
   rw 102 q9 ∷
   re 72 1 (ℓ "丼临丼") ∷
   rw 71 q10 ∷
   rw⁻ 72 q11 ∷
   rw 73 q12 ∷
   re 71 3 (ℓ "乄") ∷
   rw 72 q13 ∷
   re 74 1 (ℓ "丼临丼") ∷
   rw 73 q10 ∷
   rw⁻ 74 q11 ∷
   rw 75 q12 ∷
   re 73 3 (ℓ "乄") ∷
   rw 74 q13 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 75 q10 ∷
   rw⁻ 76 q14 ∷
   rw 77 q12 ∷
   re 75 3 (ℓ "丧") ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 76 q10 ∷
   rw⁻ 77 q14 ∷
   rw 78 q12 ∷
   re 76 3 (ℓ "丧") ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 77 q10 ∷
   rw⁻ 78 q14 ∷
   rw 79 q12 ∷
   re 77 3 (ℓ "丧") ∷
   re 79 1 (ℓ "丼临丼") ∷
   rw 78 q10 ∷
   rw⁻ 79 q11 ∷
   rw 80 q12 ∷
   re 78 3 (ℓ "乄") ∷
   rw 79 q13 ∷
   re 81 1 (ℓ "丼丠丼") ∷
   rw 80 q10 ∷
   rw⁻ 81 q14 ∷
   rw 82 q12 ∷
   re 80 3 (ℓ "丧") ∷
   re 82 1 (ℓ "丼丠丼") ∷
   rw 81 q10 ∷
   rw⁻ 82 q14 ∷
   rw 83 q12 ∷
   re 81 3 (ℓ "丧") ∷
   re 83 1 (ℓ "丼丠丼") ∷
   rw 82 q10 ∷
   rw⁻ 83 q14 ∷
   rw 84 q12 ∷
   re 82 3 (ℓ "丧") ∷
   re 84 1 (ℓ "丼丠丼") ∷
   rw 83 q10 ∷
   rw⁻ 84 q14 ∷
   rw 85 q12 ∷
   re 83 3 (ℓ "丧") ∷
   re 85 1 (ℓ "丼丠丼") ∷
   rw 84 q10 ∷
   rw⁻ 85 q14 ∷
   rw 86 q12 ∷
   re 84 3 (ℓ "丧") ∷
   re 86 1 (ℓ "丼丠丼") ∷
   rw 85 q10 ∷
   rw⁻ 86 q14 ∷
   rw 87 q12 ∷
   re 85 3 (ℓ "丧") ∷
   rw 65 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 464 W
  q20 : Eqn
  q20 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q21 : Eqn
  q21 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = wE 886 W
  q23 : Eqn
  q23 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CX13 X1]: 109 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX13-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒乀丒") ⟫ʷ ≈ ⟪ (ℓ "丒乀丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX13-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒乀丒") (ℓ "丒乀丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 32 q16 ∷
   rw 31 q17 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q18 ∷
   rw 29 q17 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q18 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q18 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q18 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q18 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q18 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q18 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q18 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q18 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q18 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q18 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q18 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q18 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q18 ∷
   rw 15 q19 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q18 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q18 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q18 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q18 ∷
   rw 10 q19 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q18 ∷
   rw 8 q19 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q18 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q18 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 1 q22 ∷
   rw⁻ 0 q17 ∷
   rw 3 q16 ∷
   re 1 3 (ℓ "乀") ∷
   rw⁻ 2 q17 ∷
   rw⁻ 3 q21 ∷
   rw⁻ 4 q21 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 6 q21 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 8 q20 ∷
   rw 11 q16 ∷
   re 9 3 (ℓ "乀") ∷
   rw 12 q16 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q23 ∷
   rw 14 q16 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q23 ∷
   rw 16 q16 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q16 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q16 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q16 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q23 ∷
   rw 21 q16 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q16 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q16 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q16 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q16 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q16 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q16 ∷
   re 25 3 (ℓ "乀") ∷
   rw 28 q16 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q16 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q16 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q16 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q16 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q16 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q18 ∷ []) Eq.refl
