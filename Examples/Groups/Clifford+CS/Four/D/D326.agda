{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D326 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q4 : Eqn
  q4 = wE 880 W
  q5 : Eqn
  q5 = wE 157 W
  q6 : Eqn
  q6 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q7 : Eqn
  q7 = wE 158 W
  q8 : Eqn
  q8 = wE 881 W
  q9 : Eqn
  q9 = wE 946 W
  q10 : Eqn
  q10 = wE 5 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 799 W
  q16 : Eqn
  q16 = wE 142 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 31 W
  q19 : Eqn
  q19 = wE 36 W
  q20 : Eqn
  q20 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q21 : Eqn
  q21 = wE 37 W
  q22 : Eqn
  q22 = wE 883 W
  q23 : Eqn
  q23 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q24 : Eqn
  q24 = wE 948 W
  q25 : Eqn
  q25 = wE 665 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part4: 483 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part4 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠丠临丠丠乀中中丒乏乀丼丠丼乏丒中中中乑业中中中中中中中中中乀中中中乑中中乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part4 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠丠临丠丠乀中中丒乏乀丼丠丼乏丒中中中乑业中中中中中中中中中乀中中中乑中中乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (re 73 1 (ℓ "乏丹乏") ∷
   rw 72 q1 ∷
   re 73 5 (ℓ "中") ∷
   rw 75 q2 ∷
   rw 74 q3 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q1 ∷
   rw 74 q4 ∷
   rw⁻ 73 q3 ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q1 ∷
   rw 72 q2 ∷
   rw 71 q3 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q1 ∷
   rw 71 q4 ∷
   rw⁻ 70 q3 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q1 ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "乀") ∷
   rw 74 q5 ∷
   rw 73 q6 ∷
   rw 72 q7 ∷
   re 72 1 (ℓ "乏丹乏") ∷
   rw 71 q1 ∷
   re 72 5 (ℓ "中") ∷
   rw 74 q2 ∷
   rw 73 q3 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q1 ∷
   rw 73 q4 ∷
   rw⁻ 72 q3 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q1 ∷
   rw 71 q2 ∷
   rw 70 q3 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q1 ∷
   rw 70 q4 ∷
   rw⁻ 69 q3 ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q1 ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "乀") ∷
   rw 73 q5 ∷
   rw 72 q6 ∷
   rw 71 q7 ∷
   re 71 1 (ℓ "乏丹乏") ∷
   rw 70 q1 ∷
   re 71 5 (ℓ "中") ∷
   rw 73 q2 ∷
   rw 72 q3 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q1 ∷
   rw 72 q4 ∷
   rw⁻ 71 q3 ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q1 ∷
   rw 68 q8 ∷
   rw 62 q9 ∷
   rw 111 q10 ∷
   rw 110 q11 ∷
   rw 109 q11 ∷
   rw 108 q11 ∷
   rw 107 q11 ∷
   rw 106 q11 ∷
   rw 105 q11 ∷
   rw⁻ 104 q12 ∷
   rw 103 q13 ∷
   rw 102 q11 ∷
   rw 101 q11 ∷
   rw 100 q11 ∷
   rw⁻ 99 q12 ∷
   rw 98 q13 ∷
   rw⁻ 97 q12 ∷
   rw 96 q13 ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw⁻ 97 q14 ∷
   rw 96 q11 ∷
   rw⁻ 95 q14 ∷
   re 96 3 (ℓ "丽") ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw⁻ 96 q14 ∷
   rw 95 q11 ∷
   rw⁻ 94 q14 ∷
   re 95 3 (ℓ "丽") ∷
   re 93 1 (ℓ "乏乄乏") ∷
   rw⁻ 95 q14 ∷
   rw 94 q13 ∷
   rw⁻ 93 q14 ∷
   re 94 3 (ℓ "乔") ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw⁻ 94 q14 ∷
   rw 93 q11 ∷
   rw⁻ 92 q14 ∷
   re 93 3 (ℓ "丽") ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw⁻ 93 q14 ∷
   rw 92 q11 ∷
   rw⁻ 91 q14 ∷
   re 92 3 (ℓ "丽") ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw⁻ 92 q14 ∷
   rw 91 q11 ∷
   rw⁻ 90 q14 ∷
   re 91 3 (ℓ "丽") ∷
   rw 91 q15 ∷
   rw 90 q16 ∷
   rw 91 q12 ∷
   rw 92 q16 ∷
   rw 93 q12 ∷
   rw 94 q17 ∷
   rw 95 q17 ∷
   rw 96 q17 ∷
   rw 97 q16 ∷
   rw 98 q12 ∷
   rw 99 q17 ∷
   rw 100 q17 ∷
   rw 101 q17 ∷
   rw 102 q17 ∷
   rw 103 q17 ∷
   rw 104 q17 ∷
   re 106 1 (ℓ "乏丶乏") ∷
   rw 105 q14 ∷
   rw 106 q17 ∷
   rw 107 q14 ∷
   re 105 3 (ℓ "中") ∷
   re 107 1 (ℓ "乏丶乏") ∷
   rw 106 q14 ∷
   rw 107 q17 ∷
   rw 108 q14 ∷
   re 106 3 (ℓ "中") ∷
   re 108 1 (ℓ "乏丶乏") ∷
   rw 107 q14 ∷
   rw 108 q17 ∷
   rw 109 q14 ∷
   re 107 3 (ℓ "中") ∷
   re 109 1 (ℓ "乏乇乏") ∷
   rw 108 q14 ∷
   rw 109 q16 ∷
   rw 110 q14 ∷
   re 108 3 (ℓ "乑") ∷
   re 110 1 (ℓ "乏丶乏") ∷
   rw 109 q14 ∷
   rw 110 q17 ∷
   rw 111 q14 ∷
   re 109 3 (ℓ "中") ∷
   re 111 1 (ℓ "乏丶乏") ∷
   rw 110 q14 ∷
   rw 111 q17 ∷
   rw 112 q14 ∷
   re 110 3 (ℓ "中") ∷
   rw 111 q18 ∷
   re 90 1 (ℓ "丼临丼") ∷
   rw 89 q19 ∷
   rw⁻ 90 q20 ∷
   rw 91 q21 ∷
   re 89 3 (ℓ "乄") ∷
   rw 90 q22 ∷
   re 92 1 (ℓ "丼临丼") ∷
   rw 91 q19 ∷
   rw⁻ 92 q20 ∷
   rw 93 q21 ∷
   re 91 3 (ℓ "乄") ∷
   rw 92 q22 ∷
   re 94 1 (ℓ "丼丠丼") ∷
   rw 93 q19 ∷
   rw⁻ 94 q6 ∷
   rw 95 q21 ∷
   re 93 3 (ℓ "丧") ∷
   re 95 1 (ℓ "丼丠丼") ∷
   rw 94 q19 ∷
   rw⁻ 95 q6 ∷
   rw 96 q21 ∷
   re 94 3 (ℓ "丧") ∷
   re 96 1 (ℓ "丼丠丼") ∷
   rw 95 q19 ∷
   rw⁻ 96 q6 ∷
   rw 97 q21 ∷
   re 95 3 (ℓ "丧") ∷
   re 97 1 (ℓ "丼临丼") ∷
   rw 96 q19 ∷
   rw⁻ 97 q20 ∷
   rw 98 q21 ∷
   re 96 3 (ℓ "乄") ∷
   rw 97 q22 ∷
   re 99 1 (ℓ "丼丠丼") ∷
   rw 98 q19 ∷
   rw⁻ 99 q6 ∷
   rw 100 q21 ∷
   re 98 3 (ℓ "丧") ∷
   re 100 1 (ℓ "丼丠丼") ∷
   rw 99 q19 ∷
   rw⁻ 100 q6 ∷
   rw 101 q21 ∷
   re 99 3 (ℓ "丧") ∷
   re 101 1 (ℓ "丼丠丼") ∷
   rw 100 q19 ∷
   rw⁻ 101 q6 ∷
   rw 102 q21 ∷
   re 100 3 (ℓ "丧") ∷
   re 102 1 (ℓ "丼丠丼") ∷
   rw 101 q19 ∷
   rw⁻ 102 q6 ∷
   rw 103 q21 ∷
   re 101 3 (ℓ "丧") ∷
   re 103 1 (ℓ "丼丠丼") ∷
   rw 102 q19 ∷
   rw⁻ 103 q6 ∷
   rw 104 q21 ∷
   re 102 3 (ℓ "丧") ∷
   re 104 1 (ℓ "丼丠丼") ∷
   rw 103 q19 ∷
   rw⁻ 104 q6 ∷
   rw 105 q21 ∷
   re 103 3 (ℓ "丧") ∷
   rw 104 q10 ∷
   rw 103 q11 ∷
   rw 102 q11 ∷
   rw 101 q11 ∷
   rw 100 q11 ∷
   rw 99 q11 ∷
   rw 98 q11 ∷
   rw⁻ 97 q12 ∷
   rw 96 q13 ∷
   rw 95 q11 ∷
   rw 94 q11 ∷
   rw 93 q11 ∷
   rw⁻ 92 q12 ∷
   rw 91 q13 ∷
   rw⁻ 90 q12 ∷
   rw 89 q13 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw⁻ 90 q14 ∷
   rw 89 q11 ∷
   rw⁻ 88 q14 ∷
   re 89 3 (ℓ "丽") ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw⁻ 89 q14 ∷
   rw 88 q11 ∷
   rw⁻ 87 q14 ∷
   re 88 3 (ℓ "丽") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw⁻ 88 q14 ∷
   rw 87 q11 ∷
   rw⁻ 86 q14 ∷
   re 87 3 (ℓ "丽") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q14 ∷
   rw 86 q11 ∷
   rw⁻ 85 q14 ∷
   re 86 3 (ℓ "丽") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw⁻ 86 q14 ∷
   rw 85 q11 ∷
   rw⁻ 84 q14 ∷
   re 85 3 (ℓ "丽") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q14 ∷
   rw 84 q11 ∷
   rw⁻ 83 q14 ∷
   re 84 3 (ℓ "丽") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q14 ∷
   rw 83 q11 ∷
   rw⁻ 82 q14 ∷
   re 83 3 (ℓ "丽") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q14 ∷
   rw 82 q11 ∷
   rw⁻ 81 q14 ∷
   re 82 3 (ℓ "丽") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q14 ∷
   rw 81 q11 ∷
   rw⁻ 80 q14 ∷
   re 81 3 (ℓ "丽") ∷
   rw⁻ 79 q23 ∷
   re 78 1 (ℓ "乏乄乏") ∷
   rw⁻ 80 q14 ∷
   rw 79 q13 ∷
   rw⁻ 78 q14 ∷
   re 79 3 (ℓ "乔") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q14 ∷
   rw 78 q11 ∷
   rw⁻ 77 q14 ∷
   re 78 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q14 ∷
   rw 77 q11 ∷
   rw⁻ 76 q14 ∷
   re 77 3 (ℓ "丽") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q14 ∷
   rw 76 q11 ∷
   rw⁻ 75 q14 ∷
   re 76 3 (ℓ "丽") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q14 ∷
   rw 75 q11 ∷
   rw⁻ 74 q14 ∷
   re 75 3 (ℓ "丽") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q14 ∷
   rw 74 q11 ∷
   rw⁻ 73 q14 ∷
   re 74 3 (ℓ "丽") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q14 ∷
   rw 73 q11 ∷
   rw⁻ 72 q14 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q24 ∷
   rw 72 q16 ∷
   rw 73 q12 ∷
   rw 74 q16 ∷
   rw 75 q12 ∷
   rw 76 q17 ∷
   rw 77 q17 ∷
   rw 78 q17 ∷
   rw 79 q16 ∷
   rw 80 q12 ∷
   rw 81 q17 ∷
   rw 82 q17 ∷
   rw 83 q17 ∷
   rw 84 q17 ∷
   rw 85 q17 ∷
   rw 86 q17 ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q14 ∷
   rw 88 q17 ∷
   rw 89 q14 ∷
   re 87 3 (ℓ "中") ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q14 ∷
   rw 89 q17 ∷
   rw 90 q14 ∷
   re 88 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏丶乏") ∷
   rw 89 q14 ∷
   rw 90 q17 ∷
   rw 91 q14 ∷
   re 89 3 (ℓ "中") ∷
   re 91 1 (ℓ "乏丶乏") ∷
   rw 90 q14 ∷
   rw 91 q17 ∷
   rw 92 q14 ∷
   re 90 3 (ℓ "中") ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q14 ∷
   rw 92 q17 ∷
   rw 93 q14 ∷
   re 91 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q14 ∷
   rw 93 q17 ∷
   rw 94 q14 ∷
   re 92 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏乇乏") ∷
   rw 93 q14 ∷
   rw 94 q16 ∷
   rw 95 q14 ∷
   re 93 3 (ℓ "乑") ∷
   rw 94 q23 ∷
   re 96 1 (ℓ "乏丶乏") ∷
   rw 95 q14 ∷
   rw 96 q17 ∷
   rw 97 q14 ∷
   re 95 3 (ℓ "中") ∷
   re 97 1 (ℓ "乏丶乏") ∷
   rw 96 q14 ∷
   rw 97 q17 ∷
   rw 98 q14 ∷
   re 96 3 (ℓ "中") ∷
   re 98 1 (ℓ "乏丶乏") ∷
   rw 97 q14 ∷
   rw 98 q17 ∷
   rw 99 q14 ∷
   re 97 3 (ℓ "中") ∷
   re 99 1 (ℓ "乏丶乏") ∷
   rw 98 q14 ∷
   rw 99 q17 ∷
   rw 100 q14 ∷
   re 98 3 (ℓ "中") ∷
   re 100 1 (ℓ "乏丶乏") ∷
   rw 99 q14 ∷
   rw 100 q17 ∷
   rw 101 q14 ∷
   re 99 3 (ℓ "中") ∷
   re 101 1 (ℓ "乏丶乏") ∷
   rw 100 q14 ∷
   rw 101 q17 ∷
   rw 102 q14 ∷
   re 100 3 (ℓ "中") ∷
   re 102 1 (ℓ "乏丶乏") ∷
   rw 101 q14 ∷
   rw 102 q17 ∷
   rw 103 q14 ∷
   re 101 3 (ℓ "中") ∷
   re 103 1 (ℓ "乏丶乏") ∷
   rw 102 q14 ∷
   rw 103 q17 ∷
   rw 104 q14 ∷
   re 102 3 (ℓ "中") ∷
   re 104 1 (ℓ "乏丶乏") ∷
   rw 103 q14 ∷
   rw 104 q17 ∷
   rw 105 q14 ∷
   re 103 3 (ℓ "中") ∷
   rw 104 q18 ∷
   re 72 1 (ℓ "丼临丼") ∷
   rw 71 q19 ∷
   rw⁻ 72 q20 ∷
   rw 73 q21 ∷
   re 71 3 (ℓ "乄") ∷
   rw 72 q22 ∷
   re 74 1 (ℓ "丼临丼") ∷
   rw 73 q19 ∷
   rw⁻ 74 q20 ∷
   rw 75 q21 ∷
   re 73 3 (ℓ "乄") ∷
   rw 74 q22 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 75 q19 ∷
   rw⁻ 76 q6 ∷
   rw 77 q21 ∷
   re 75 3 (ℓ "丧") ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 76 q19 ∷
   rw⁻ 77 q6 ∷
   rw 78 q21 ∷
   re 76 3 (ℓ "丧") ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 77 q19 ∷
   rw⁻ 78 q6 ∷
   rw 79 q21 ∷
   re 77 3 (ℓ "丧") ∷
   re 79 1 (ℓ "丼临丼") ∷
   rw 78 q19 ∷
   rw⁻ 79 q20 ∷
   rw 80 q21 ∷
   re 78 3 (ℓ "乄") ∷
   rw 79 q22 ∷
   re 81 1 (ℓ "丼丠丼") ∷
   rw 80 q19 ∷
   rw⁻ 81 q6 ∷
   rw 82 q21 ∷
   re 80 3 (ℓ "丧") ∷
   re 82 1 (ℓ "丼丠丼") ∷
   rw 81 q19 ∷
   rw⁻ 82 q6 ∷
   rw 83 q21 ∷
   re 81 3 (ℓ "丧") ∷
   re 83 1 (ℓ "丼丠丼") ∷
   rw 82 q19 ∷
   rw⁻ 83 q6 ∷
   rw 84 q21 ∷
   re 82 3 (ℓ "丧") ∷
   re 84 1 (ℓ "丼丠丼") ∷
   rw 83 q19 ∷
   rw⁻ 84 q6 ∷
   rw 85 q21 ∷
   re 83 3 (ℓ "丧") ∷
   re 85 1 (ℓ "丼丠丼") ∷
   rw 84 q19 ∷
   rw⁻ 85 q6 ∷
   rw 86 q21 ∷
   re 84 3 (ℓ "丧") ∷
   re 86 1 (ℓ "丼丠丼") ∷
   rw 85 q19 ∷
   rw⁻ 86 q6 ∷
   rw 87 q21 ∷
   re 85 3 (ℓ "丧") ∷
   rw 65 q25 ∷ []) Eq.refl
