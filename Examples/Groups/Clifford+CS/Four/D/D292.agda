{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D292 (W : Ws) where

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
  q1 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 880 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 157 W
  q6 : Eqn
  q6 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q7 : Eqn
  q7 = wE 158 W
  q8 : Eqn
  q8 = eqn (ℓ "丒业") (ℓ "业丒") (low-comm ((X ↑)) ((S ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q10 : Eqn
  q10 = wE 879 W
  q11 : Eqn
  q11 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 881 W
  q13 : Eqn
  q13 = wE 882 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 763 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = wE 36 W
  q24 : Eqn
  q24 = wE 37 W
  q25 : Eqn
  q25 = wE 883 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part3: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part3 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠临丠临临乀乑业乑业中中中乑业中中中中中丒丹中丒乏乏乀中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中乏丧並乏丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並乀中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part3 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丠丠临丠临临乀乑业乑业中中中乑业中中中中中丒丹中丒乏乏乀中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒丠丠临丠临临乀乑业乑业中中中乑业中中中乏丧並乏丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並乀中中乑中乑乑")
  (rw 86 q1 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q2 ∷
   rw 86 q3 ∷
   rw⁻ 85 q1 ∷
   rw 88 q4 ∷
   re 86 3 (ℓ "中") ∷
   rw 87 q2 ∷
   rw 84 q4 ∷
   rw 83 q1 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q2 ∷
   rw 83 q3 ∷
   rw⁻ 82 q1 ∷
   rw 85 q4 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q2 ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q4 ∷
   re 87 3 (ℓ "乀") ∷
   rw 86 q5 ∷
   rw 85 q6 ∷
   rw 84 q7 ∷
   re 84 1 (ℓ "乏丹乏") ∷
   rw 83 q2 ∷
   re 84 5 (ℓ "中") ∷
   rw 86 q4 ∷
   rw 85 q1 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q2 ∷
   rw 85 q3 ∷
   rw⁻ 84 q1 ∷
   rw 87 q4 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q2 ∷
   rw 83 q4 ∷
   rw 82 q1 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q2 ∷
   rw 82 q3 ∷
   rw⁻ 81 q1 ∷
   rw 84 q4 ∷
   re 82 3 (ℓ "中") ∷
   rw 83 q2 ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q4 ∷
   re 86 3 (ℓ "乀") ∷
   rw 85 q5 ∷
   rw 84 q6 ∷
   rw 83 q7 ∷
   re 83 1 (ℓ "乏丹乏") ∷
   rw 82 q2 ∷
   re 83 5 (ℓ "中") ∷
   rw 85 q4 ∷
   rw 84 q1 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q2 ∷
   rw 84 q3 ∷
   rw⁻ 83 q1 ∷
   rw 86 q4 ∷
   re 84 3 (ℓ "中") ∷
   rw 85 q2 ∷
   rw 82 q4 ∷
   rw 81 q1 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q2 ∷
   rw 81 q3 ∷
   rw⁻ 80 q1 ∷
   rw 83 q4 ∷
   re 81 3 (ℓ "中") ∷
   rw 82 q2 ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q4 ∷
   re 85 3 (ℓ "乀") ∷
   rw 84 q5 ∷
   rw 83 q6 ∷
   rw 82 q7 ∷
   re 82 1 (ℓ "乏丹乏") ∷
   rw 81 q2 ∷
   re 82 5 (ℓ "中") ∷
   rw 84 q4 ∷
   rw 83 q1 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q2 ∷
   rw 83 q3 ∷
   rw⁻ 82 q1 ∷
   rw 85 q4 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q2 ∷
   rw 81 q4 ∷
   rw 80 q1 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q2 ∷
   rw 80 q3 ∷
   rw⁻ 79 q1 ∷
   rw 82 q4 ∷
   re 80 3 (ℓ "中") ∷
   rw 81 q2 ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q4 ∷
   re 84 3 (ℓ "乀") ∷
   rw 83 q5 ∷
   rw 82 q6 ∷
   rw 81 q7 ∷
   re 81 1 (ℓ "乏丹乏") ∷
   rw 80 q2 ∷
   re 81 5 (ℓ "中") ∷
   rw 83 q4 ∷
   rw 82 q1 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q2 ∷
   rw 82 q3 ∷
   rw⁻ 81 q1 ∷
   rw 84 q4 ∷
   re 82 3 (ℓ "中") ∷
   rw 83 q2 ∷
   rw 80 q4 ∷
   rw 79 q1 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q2 ∷
   rw 79 q3 ∷
   rw⁻ 78 q1 ∷
   rw 81 q4 ∷
   re 79 3 (ℓ "中") ∷
   rw 80 q2 ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q4 ∷
   re 83 3 (ℓ "乀") ∷
   rw 82 q5 ∷
   rw 81 q6 ∷
   rw 80 q7 ∷
   re 80 1 (ℓ "乏丹乏") ∷
   rw 79 q2 ∷
   re 80 5 (ℓ "中") ∷
   rw 82 q4 ∷
   rw 81 q1 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q2 ∷
   rw 81 q3 ∷
   rw⁻ 80 q1 ∷
   rw 83 q4 ∷
   re 81 3 (ℓ "中") ∷
   rw 82 q2 ∷
   rw⁻ 77 q8 ∷
   rw⁻ 78 q9 ∷
   rw⁻ 79 q8 ∷
   rw 78 q4 ∷
   rw 77 q1 ∷
   re 76 1 (ℓ "乏乄乏") ∷
   rw 78 q2 ∷
   rw 77 q10 ∷
   rw⁻ 76 q1 ∷
   rw 79 q4 ∷
   re 77 3 (ℓ "乑") ∷
   rw 78 q2 ∷
   re 77 1 (ℓ "乏丼临丼乏") ∷
   rw 83 q4 ∷
   re 81 3 (ℓ "乀") ∷
   rw 80 q5 ∷
   rw 79 q11 ∷
   rw 78 q7 ∷
   re 78 1 (ℓ "乏丹乏") ∷
   rw 77 q2 ∷
   re 78 5 (ℓ "乑") ∷
   rw 80 q4 ∷
   rw 79 q1 ∷
   re 78 1 (ℓ "乏乄乏") ∷
   rw 80 q2 ∷
   rw 79 q10 ∷
   rw⁻ 78 q1 ∷
   rw 81 q4 ∷
   re 79 3 (ℓ "乑") ∷
   rw 80 q2 ∷
   rw 77 q4 ∷
   rw 76 q1 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q2 ∷
   rw 76 q3 ∷
   rw⁻ 75 q1 ∷
   rw 78 q4 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q2 ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q4 ∷
   re 80 3 (ℓ "乀") ∷
   rw 79 q5 ∷
   rw 78 q6 ∷
   rw 77 q7 ∷
   re 77 1 (ℓ "乏丹乏") ∷
   rw 76 q2 ∷
   re 77 5 (ℓ "中") ∷
   rw 79 q4 ∷
   rw 78 q1 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   rw⁻ 77 q1 ∷
   rw 80 q4 ∷
   re 78 3 (ℓ "中") ∷
   rw 79 q2 ∷
   rw 76 q4 ∷
   rw 75 q1 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q2 ∷
   rw 75 q3 ∷
   rw⁻ 74 q1 ∷
   rw 77 q4 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q2 ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q4 ∷
   re 79 3 (ℓ "乀") ∷
   rw 78 q5 ∷
   rw 77 q6 ∷
   rw 76 q7 ∷
   re 76 1 (ℓ "乏丹乏") ∷
   rw 75 q2 ∷
   re 76 5 (ℓ "中") ∷
   rw 78 q4 ∷
   rw 77 q1 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q2 ∷
   rw 77 q3 ∷
   rw⁻ 76 q1 ∷
   rw 79 q4 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q2 ∷
   rw 75 q4 ∷
   rw 74 q1 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q2 ∷
   rw 74 q3 ∷
   rw⁻ 73 q1 ∷
   rw 76 q4 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q2 ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q4 ∷
   re 78 3 (ℓ "乀") ∷
   rw 77 q5 ∷
   rw 76 q6 ∷
   rw 75 q7 ∷
   re 75 1 (ℓ "乏丹乏") ∷
   rw 74 q2 ∷
   re 75 5 (ℓ "中") ∷
   rw 77 q4 ∷
   rw 76 q1 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q2 ∷
   rw 76 q3 ∷
   rw⁻ 75 q1 ∷
   rw 78 q4 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q2 ∷
   rw⁻ 72 q8 ∷
   rw⁻ 73 q9 ∷
   rw⁻ 74 q8 ∷
   rw 73 q4 ∷
   rw 72 q1 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw 73 q2 ∷
   rw 72 q10 ∷
   rw⁻ 71 q1 ∷
   rw 74 q4 ∷
   re 72 3 (ℓ "乑") ∷
   rw 73 q2 ∷
   re 72 1 (ℓ "乏丼临丼乏") ∷
   rw 78 q4 ∷
   re 76 3 (ℓ "乀") ∷
   rw 75 q5 ∷
   rw 74 q11 ∷
   rw 73 q7 ∷
   re 73 1 (ℓ "乏丹乏") ∷
   rw 72 q2 ∷
   re 73 5 (ℓ "乑") ∷
   rw 75 q4 ∷
   rw 74 q1 ∷
   re 73 1 (ℓ "乏乄乏") ∷
   rw 75 q2 ∷
   rw 74 q10 ∷
   rw⁻ 73 q1 ∷
   rw 76 q4 ∷
   re 74 3 (ℓ "乑") ∷
   rw 75 q2 ∷
   rw⁻ 70 q8 ∷
   rw⁻ 71 q9 ∷
   rw⁻ 72 q8 ∷
   rw 71 q4 ∷
   rw 70 q1 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw 71 q2 ∷
   rw 70 q10 ∷
   rw⁻ 69 q1 ∷
   rw 72 q4 ∷
   re 70 3 (ℓ "乑") ∷
   rw 71 q2 ∷
   re 70 1 (ℓ "乏丼临丼乏") ∷
   rw 76 q4 ∷
   re 74 3 (ℓ "乀") ∷
   rw 73 q5 ∷
   rw 72 q11 ∷
   rw 71 q7 ∷
   re 71 1 (ℓ "乏丹乏") ∷
   rw 70 q2 ∷
   re 71 5 (ℓ "乑") ∷
   rw 73 q4 ∷
   rw 72 q1 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw 73 q2 ∷
   rw 72 q10 ∷
   rw⁻ 71 q1 ∷
   rw 74 q4 ∷
   re 72 3 (ℓ "乑") ∷
   rw 73 q2 ∷
   rw 68 q12 ∷
   rw 62 q13 ∷
   rw 109 q14 ∷
   rw 108 q15 ∷
   rw 107 q15 ∷
   rw 106 q15 ∷
   rw 105 q15 ∷
   rw 104 q15 ∷
   rw 103 q15 ∷
   rw⁻ 102 q16 ∷
   rw 101 q17 ∷
   rw 100 q15 ∷
   rw 99 q15 ∷
   rw 98 q15 ∷
   rw⁻ 97 q16 ∷
   rw 96 q17 ∷
   rw⁻ 95 q16 ∷
   rw 94 q17 ∷
   re 93 1 (ℓ "乏乄乏") ∷
   rw⁻ 95 q18 ∷
   rw 94 q17 ∷
   rw⁻ 93 q18 ∷
   re 94 3 (ℓ "乔") ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw⁻ 94 q18 ∷
   rw 93 q17 ∷
   rw⁻ 92 q18 ∷
   re 93 3 (ℓ "乔") ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw⁻ 93 q18 ∷
   rw 92 q15 ∷
   rw⁻ 91 q18 ∷
   re 92 3 (ℓ "丽") ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw⁻ 92 q18 ∷
   rw 91 q17 ∷
   rw⁻ 90 q18 ∷
   re 91 3 (ℓ "乔") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw⁻ 91 q18 ∷
   rw 90 q15 ∷
   rw⁻ 89 q18 ∷
   re 90 3 (ℓ "丽") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw⁻ 90 q18 ∷
   rw 89 q15 ∷
   rw⁻ 88 q18 ∷
   re 89 3 (ℓ "丽") ∷
   rw 89 q19 ∷
   rw 88 q20 ∷
   rw 89 q16 ∷
   rw 90 q20 ∷
   rw 91 q16 ∷
   rw 92 q21 ∷
   rw 93 q21 ∷
   rw 94 q21 ∷
   rw 95 q20 ∷
   rw 96 q16 ∷
   rw 97 q21 ∷
   rw 98 q21 ∷
   rw 99 q21 ∷
   rw 100 q21 ∷
   rw 101 q21 ∷
   rw 102 q21 ∷
   re 104 1 (ℓ "乏丶乏") ∷
   rw 103 q18 ∷
   rw 104 q21 ∷
   rw 105 q18 ∷
   re 103 3 (ℓ "中") ∷
   re 105 1 (ℓ "乏丶乏") ∷
   rw 104 q18 ∷
   rw 105 q21 ∷
   rw 106 q18 ∷
   re 104 3 (ℓ "中") ∷
   re 106 1 (ℓ "乏乇乏") ∷
   rw 105 q18 ∷
   rw 106 q20 ∷
   rw 107 q18 ∷
   re 105 3 (ℓ "乑") ∷
   re 107 1 (ℓ "乏丶乏") ∷
   rw 106 q18 ∷
   rw 107 q21 ∷
   rw 108 q18 ∷
   re 106 3 (ℓ "中") ∷
   re 108 1 (ℓ "乏乇乏") ∷
   rw 107 q18 ∷
   rw 108 q20 ∷
   rw 109 q18 ∷
   re 107 3 (ℓ "乑") ∷
   re 109 1 (ℓ "乏乇乏") ∷
   rw 108 q18 ∷
   rw 109 q20 ∷
   rw 110 q18 ∷
   re 108 3 (ℓ "乑") ∷
   rw 109 q22 ∷
   re 88 1 (ℓ "丼临丼") ∷
   rw 87 q23 ∷
   rw⁻ 88 q11 ∷
   rw 89 q24 ∷
   re 87 3 (ℓ "乄") ∷
   rw 88 q25 ∷
   re 90 1 (ℓ "丼临丼") ∷
   rw 89 q23 ∷
   rw⁻ 90 q11 ∷
   rw 91 q24 ∷
   re 89 3 (ℓ "乄") ∷
   rw 90 q25 ∷
   re 92 1 (ℓ "丼丠丼") ∷
   rw 91 q23 ∷
   rw⁻ 92 q6 ∷
   rw 93 q24 ∷
   re 91 3 (ℓ "丧") ∷
   re 93 1 (ℓ "丼丠丼") ∷
   rw 92 q23 ∷
   rw⁻ 93 q6 ∷
   rw 94 q24 ∷
   re 92 3 (ℓ "丧") ∷
   re 94 1 (ℓ "丼丠丼") ∷
   rw 93 q23 ∷
   rw⁻ 94 q6 ∷
   rw 95 q24 ∷
   re 93 3 (ℓ "丧") ∷
   re 95 1 (ℓ "丼临丼") ∷
   rw 94 q23 ∷
   rw⁻ 95 q11 ∷
   rw 96 q24 ∷
   re 94 3 (ℓ "乄") ∷
   rw 95 q25 ∷
   re 97 1 (ℓ "丼丠丼") ∷
   rw 96 q23 ∷
   rw⁻ 97 q6 ∷
   rw 98 q24 ∷
   re 96 3 (ℓ "丧") ∷
   re 98 1 (ℓ "丼丠丼") ∷
   rw 97 q23 ∷
   rw⁻ 98 q6 ∷
   rw 99 q24 ∷
   re 97 3 (ℓ "丧") ∷
   re 99 1 (ℓ "丼丠丼") ∷
   rw 98 q23 ∷
   rw⁻ 99 q6 ∷
   rw 100 q24 ∷
   re 98 3 (ℓ "丧") ∷
   re 100 1 (ℓ "丼丠丼") ∷
   rw 99 q23 ∷
   rw⁻ 100 q6 ∷
   rw 101 q24 ∷
   re 99 3 (ℓ "丧") ∷
   re 101 1 (ℓ "丼丠丼") ∷
   rw 100 q23 ∷
   rw⁻ 101 q6 ∷
   rw 102 q24 ∷
   re 100 3 (ℓ "丧") ∷
   re 102 1 (ℓ "丼丠丼") ∷
   rw 101 q23 ∷
   rw⁻ 102 q6 ∷
   rw 103 q24 ∷
   re 101 3 (ℓ "丧") ∷
   rw 102 q14 ∷
   rw 101 q15 ∷
   rw 100 q15 ∷
   rw 99 q15 ∷
   rw 98 q15 ∷
   rw 97 q15 ∷
   rw 96 q15 ∷
   rw⁻ 95 q16 ∷
   rw 94 q17 ∷
   rw 93 q15 ∷
   rw 92 q15 ∷
   rw 91 q15 ∷
   rw⁻ 90 q16 ∷
   rw 89 q17 ∷
   rw⁻ 88 q16 ∷
   rw 87 q17 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw⁻ 88 q18 ∷
   rw 87 q15 ∷
   rw⁻ 86 q18 ∷
   re 87 3 (ℓ "丽") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q18 ∷
   rw 86 q15 ∷
   rw⁻ 85 q18 ∷
   re 86 3 (ℓ "丽") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw⁻ 86 q18 ∷ []) Eq.refl
