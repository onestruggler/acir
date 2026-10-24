{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D343 (W : Ws) where

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
  q2 = wE 880 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 157 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = wE 158 W
  q7 : Eqn
  q7 = eqn (ℓ "丒且") (ℓ "且丒") (low-comm ((X ↑)) (S))
  q8 : Eqn
  q8 = wE 625 W
  q9 : Eqn
  q9 = wE 879 W
  q10 : Eqn
  q10 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q11 : Eqn
  q11 = wE 956 W
  q12 : Eqn
  q12 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q13 : Eqn
  q13 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = wE 882 W
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 963 W
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 142 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = wE 36 W
  q26 : Eqn
  q26 = wE 37 W
  q27 : Eqn
  q27 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part5: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part5 : ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丒乏丹乏丼丠丼乏乏丒丧丹丧丧乄丧乄乄中中中中中中乑业中中中中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中乑业中中中中中乏丼丠丼乀乏中中中丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part5 = derive (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丒乏丹乏丼丠丼乏乏丒丧丹丧丧乄丧乄乄中中中中中中乑业中中中中中中中中中") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中乑业中中中中中乏丼丠丼乀乏中中中丧丧乄丧乄乄")
  (re 95 5 (ℓ "中") ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q1 ∷
   re 93 3 (ℓ "乀") ∷
   rw 94 q2 ∷
   rw 91 q2 ∷
   re 93 1 (ℓ "乏丹乏") ∷
   rw 92 q3 ∷
   re 93 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丼丠丼乏") ∷
   rw 99 q3 ∷
   re 97 3 (ℓ "乀") ∷
   rw 96 q4 ∷
   rw 95 q5 ∷
   rw 94 q6 ∷
   re 94 1 (ℓ "乏丹乏") ∷
   rw 93 q1 ∷
   re 94 5 (ℓ "中") ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q1 ∷
   re 92 3 (ℓ "乀") ∷
   rw 93 q2 ∷
   rw 90 q2 ∷
   re 92 1 (ℓ "乏丹乏") ∷
   rw 91 q3 ∷
   re 92 3 (ℓ "中") ∷
   re 92 1 (ℓ "乏丼丠丼乏") ∷
   rw 98 q3 ∷
   re 96 3 (ℓ "乀") ∷
   rw 95 q4 ∷
   rw 94 q5 ∷
   rw 93 q6 ∷
   re 93 1 (ℓ "乏丹乏") ∷
   rw 92 q1 ∷
   re 93 5 (ℓ "中") ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw 95 q1 ∷
   re 91 3 (ℓ "乀") ∷
   rw 92 q2 ∷
   rw 89 q2 ∷
   re 91 1 (ℓ "乏丹乏") ∷
   rw 90 q3 ∷
   re 91 3 (ℓ "中") ∷
   re 91 1 (ℓ "乏丼丠丼乏") ∷
   rw 97 q3 ∷
   re 95 3 (ℓ "乀") ∷
   rw 94 q4 ∷
   rw 93 q5 ∷
   rw 92 q6 ∷
   re 92 1 (ℓ "乏丹乏") ∷
   rw 91 q1 ∷
   re 92 5 (ℓ "中") ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q1 ∷
   re 90 3 (ℓ "乀") ∷
   rw 91 q2 ∷
   rw 88 q2 ∷
   re 90 1 (ℓ "乏丹乏") ∷
   rw 89 q3 ∷
   re 90 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 96 q3 ∷
   re 94 3 (ℓ "乀") ∷
   rw 93 q4 ∷
   rw 92 q5 ∷
   rw 91 q6 ∷
   re 91 1 (ℓ "乏丹乏") ∷
   rw 90 q1 ∷
   re 91 5 (ℓ "中") ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q1 ∷
   re 89 3 (ℓ "乀") ∷
   rw 90 q2 ∷
   rw⁻ 87 q7 ∷
   rw 88 q8 ∷
   rw⁻ 89 q7 ∷
   rw 86 q9 ∷
   re 88 1 (ℓ "乏丹乏") ∷
   rw 87 q3 ∷
   re 88 3 (ℓ "乑") ∷
   re 88 1 (ℓ "乏丼临丼乏") ∷
   rw 94 q3 ∷
   re 92 3 (ℓ "乀") ∷
   rw 91 q4 ∷
   rw 90 q10 ∷
   rw 89 q6 ∷
   re 89 1 (ℓ "乏丹乏") ∷
   rw 88 q1 ∷
   re 89 5 (ℓ "乑") ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw 91 q1 ∷
   re 87 3 (ℓ "乀") ∷
   rw 88 q9 ∷
   rw 85 q2 ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 86 q3 ∷
   re 87 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 93 q3 ∷
   re 91 3 (ℓ "乀") ∷
   rw 90 q4 ∷
   rw 89 q5 ∷
   rw 88 q6 ∷
   re 88 1 (ℓ "乏丹乏") ∷
   rw 87 q1 ∷
   re 88 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q1 ∷
   re 86 3 (ℓ "乀") ∷
   rw 87 q2 ∷
   rw 84 q2 ∷
   re 86 1 (ℓ "乏丹乏") ∷
   rw 85 q3 ∷
   re 86 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q3 ∷
   re 90 3 (ℓ "乀") ∷
   rw 89 q4 ∷
   rw 88 q5 ∷
   rw 87 q6 ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 86 q1 ∷
   re 87 5 (ℓ "中") ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q1 ∷
   re 85 3 (ℓ "乀") ∷
   rw 86 q2 ∷
   rw 83 q2 ∷
   re 85 1 (ℓ "乏丹乏") ∷
   rw 84 q3 ∷
   re 85 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q3 ∷
   re 89 3 (ℓ "乀") ∷
   rw 88 q4 ∷
   rw 87 q5 ∷
   rw 86 q6 ∷
   re 86 1 (ℓ "乏丹乏") ∷
   rw 85 q1 ∷
   re 86 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q1 ∷
   re 84 3 (ℓ "乀") ∷
   rw 85 q2 ∷
   rw⁻ 82 q7 ∷
   rw 83 q8 ∷
   rw⁻ 84 q7 ∷
   rw 81 q9 ∷
   re 83 1 (ℓ "乏丹乏") ∷
   rw 82 q3 ∷
   re 83 3 (ℓ "乑") ∷
   re 83 1 (ℓ "乏丼临丼乏") ∷
   rw 89 q3 ∷
   re 87 3 (ℓ "乀") ∷
   rw 86 q4 ∷
   rw 85 q10 ∷
   rw 84 q6 ∷
   re 84 1 (ℓ "乏丹乏") ∷
   rw 83 q1 ∷
   re 84 5 (ℓ "乑") ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw 86 q1 ∷
   re 82 3 (ℓ "乀") ∷
   rw 83 q9 ∷
   rw⁻ 80 q7 ∷
   rw 81 q8 ∷
   rw⁻ 82 q7 ∷
   rw 79 q9 ∷
   re 81 1 (ℓ "乏丹乏") ∷
   rw 80 q3 ∷
   re 81 3 (ℓ "乑") ∷
   re 81 1 (ℓ "乏丼临丼乏") ∷
   rw 87 q3 ∷
   re 85 3 (ℓ "乀") ∷
   rw 84 q4 ∷
   rw 83 q10 ∷
   rw 82 q6 ∷
   re 82 1 (ℓ "乏丹乏") ∷
   rw 81 q1 ∷
   re 82 5 (ℓ "乑") ∷
   re 82 1 (ℓ "乏乄乏") ∷
   rw 84 q1 ∷
   re 80 3 (ℓ "乀") ∷
   rw 81 q9 ∷
   rw 78 q11 ∷
   rw 81 q3 ∷
   rw 80 q12 ∷
   re 79 1 (ℓ "乏丹乏") ∷
   rw 81 q1 ∷
   rw 78 q12 ∷
   rw 77 q13 ∷
   rw 76 q13 ∷
   rw 75 q14 ∷
   rw 74 q13 ∷
   rw 73 q14 ∷
   rw 72 q14 ∷
   rw 73 q15 ∷
   rw⁻ 72 q12 ∷
   rw 75 q3 ∷
   re 73 3 (ℓ "乀") ∷
   rw⁻ 74 q12 ∷
   rw⁻ 75 q14 ∷
   rw⁻ 76 q14 ∷
   rw⁻ 77 q13 ∷
   rw⁻ 78 q14 ∷
   rw⁻ 79 q13 ∷
   rw⁻ 80 q13 ∷
   rw 81 q1 ∷
   rw 121 q16 ∷
   re 120 1 (ℓ "乏丧乏") ∷
   rw⁻ 122 q17 ∷
   rw 121 q18 ∷
   rw⁻ 120 q17 ∷
   re 121 3 (ℓ "丽") ∷
   re 119 1 (ℓ "乏丧乏") ∷
   rw⁻ 121 q17 ∷
   rw 120 q18 ∷
   rw⁻ 119 q17 ∷
   re 120 3 (ℓ "丽") ∷
   re 118 1 (ℓ "乏丧乏") ∷
   rw⁻ 120 q17 ∷
   rw 119 q18 ∷
   rw⁻ 118 q17 ∷
   re 119 3 (ℓ "丽") ∷
   re 117 1 (ℓ "乏丧乏") ∷
   rw⁻ 119 q17 ∷
   rw 118 q18 ∷
   rw⁻ 117 q17 ∷
   re 118 3 (ℓ "丽") ∷
   re 116 1 (ℓ "乏丧乏") ∷
   rw⁻ 118 q17 ∷
   rw 117 q18 ∷
   rw⁻ 116 q17 ∷
   re 117 3 (ℓ "丽") ∷
   re 115 1 (ℓ "乏丧乏") ∷
   rw⁻ 117 q17 ∷
   rw 116 q18 ∷
   rw⁻ 115 q17 ∷
   re 116 3 (ℓ "丽") ∷
   re 114 1 (ℓ "乏丧乏") ∷
   rw⁻ 116 q17 ∷
   rw 115 q18 ∷
   rw⁻ 114 q17 ∷
   re 115 3 (ℓ "丽") ∷
   re 113 1 (ℓ "乏丧乏") ∷
   rw⁻ 115 q17 ∷
   rw 114 q18 ∷
   rw⁻ 113 q17 ∷
   re 114 3 (ℓ "丽") ∷
   re 112 1 (ℓ "乏丧乏") ∷
   rw⁻ 114 q17 ∷
   rw 113 q18 ∷
   rw⁻ 112 q17 ∷
   re 113 3 (ℓ "丽") ∷
   rw⁻ 111 q19 ∷
   re 110 1 (ℓ "乏乄乏") ∷
   rw⁻ 112 q17 ∷
   rw 111 q20 ∷
   rw⁻ 110 q17 ∷
   re 111 3 (ℓ "乔") ∷
   re 109 1 (ℓ "乏丧乏") ∷
   rw⁻ 111 q17 ∷
   rw 110 q18 ∷
   rw⁻ 109 q17 ∷
   re 110 3 (ℓ "丽") ∷
   re 108 1 (ℓ "乏丧乏") ∷
   rw⁻ 110 q17 ∷
   rw 109 q18 ∷
   rw⁻ 108 q17 ∷
   re 109 3 (ℓ "丽") ∷
   re 107 1 (ℓ "乏丧乏") ∷
   rw⁻ 109 q17 ∷
   rw 108 q18 ∷
   rw⁻ 107 q17 ∷
   re 108 3 (ℓ "丽") ∷
   re 106 1 (ℓ "乏丧乏") ∷
   rw⁻ 108 q17 ∷
   rw 107 q18 ∷
   rw⁻ 106 q17 ∷
   re 107 3 (ℓ "丽") ∷
   re 105 1 (ℓ "乏丧乏") ∷
   rw⁻ 107 q17 ∷
   rw 106 q18 ∷
   rw⁻ 105 q17 ∷
   re 106 3 (ℓ "丽") ∷
   re 104 1 (ℓ "乏丧乏") ∷
   rw⁻ 106 q17 ∷
   rw 105 q18 ∷
   rw⁻ 104 q17 ∷
   re 105 3 (ℓ "丽") ∷
   rw 103 q20 ∷
   rw 102 q20 ∷
   rw 101 q18 ∷
   rw 100 q20 ∷
   rw 99 q18 ∷
   rw 98 q18 ∷
   rw 99 q21 ∷
   re 99 1 (ℓ "乏丶乏") ∷
   rw 98 q17 ∷
   rw 99 q22 ∷
   rw 100 q17 ∷
   re 98 3 (ℓ "中") ∷
   re 100 1 (ℓ "乏丶乏") ∷
   rw 99 q17 ∷
   rw 100 q22 ∷
   rw 101 q17 ∷
   re 99 3 (ℓ "中") ∷
   re 101 1 (ℓ "乏丶乏") ∷
   rw 100 q17 ∷
   rw 101 q22 ∷
   rw 102 q17 ∷
   re 100 3 (ℓ "中") ∷
   re 102 1 (ℓ "乏丶乏") ∷
   rw 101 q17 ∷
   rw 102 q22 ∷
   rw 103 q17 ∷
   re 101 3 (ℓ "中") ∷
   re 103 1 (ℓ "乏丶乏") ∷
   rw 102 q17 ∷
   rw 103 q22 ∷
   rw 104 q17 ∷
   re 102 3 (ℓ "中") ∷
   re 104 1 (ℓ "乏丶乏") ∷
   rw 103 q17 ∷
   rw 104 q22 ∷
   rw 105 q17 ∷
   re 103 3 (ℓ "中") ∷
   re 105 1 (ℓ "乏乇乏") ∷
   rw 104 q17 ∷
   rw 105 q23 ∷
   rw 106 q17 ∷
   re 104 3 (ℓ "乑") ∷
   rw 105 q19 ∷
   re 107 1 (ℓ "乏丶乏") ∷
   rw 106 q17 ∷
   rw 107 q22 ∷
   rw 108 q17 ∷
   re 106 3 (ℓ "中") ∷
   re 108 1 (ℓ "乏丶乏") ∷
   rw 107 q17 ∷
   rw 108 q22 ∷
   rw 109 q17 ∷
   re 107 3 (ℓ "中") ∷
   re 109 1 (ℓ "乏丶乏") ∷
   rw 108 q17 ∷
   rw 109 q22 ∷
   rw 110 q17 ∷
   re 108 3 (ℓ "中") ∷
   re 110 1 (ℓ "乏丶乏") ∷
   rw 109 q17 ∷
   rw 110 q22 ∷
   rw 111 q17 ∷
   re 109 3 (ℓ "中") ∷
   re 111 1 (ℓ "乏丶乏") ∷
   rw 110 q17 ∷
   rw 111 q22 ∷
   rw 112 q17 ∷
   re 110 3 (ℓ "中") ∷
   re 112 1 (ℓ "乏丶乏") ∷
   rw 111 q17 ∷
   rw 112 q22 ∷
   rw 113 q17 ∷
   re 111 3 (ℓ "中") ∷
   re 113 1 (ℓ "乏丶乏") ∷
   rw 112 q17 ∷
   rw 113 q22 ∷
   rw 114 q17 ∷
   re 112 3 (ℓ "中") ∷
   re 114 1 (ℓ "乏丶乏") ∷
   rw 113 q17 ∷
   rw 114 q22 ∷
   rw 115 q17 ∷
   re 113 3 (ℓ "中") ∷
   re 115 1 (ℓ "乏丶乏") ∷
   rw 114 q17 ∷
   rw 115 q22 ∷
   rw 116 q17 ∷
   re 114 3 (ℓ "中") ∷
   rw 115 q22 ∷
   rw 116 q22 ∷
   rw 117 q23 ∷
   rw 118 q22 ∷
   rw 119 q23 ∷
   rw 120 q23 ∷
   rw 121 q24 ∷
   re 98 1 (ℓ "乏丼丠丼乏") ∷
   rw 97 q3 ∷
   re 98 3 (ℓ "乀") ∷
   rw 98 q25 ∷
   rw⁻ 99 q5 ∷
   rw 100 q26 ∷
   re 101 1 (ℓ "乏丹乏") ∷
   rw 103 q1 ∷
   re 97 5 (ℓ "中") ∷
   re 99 1 (ℓ "乏丼丠丼乏") ∷
   rw 98 q3 ∷
   re 99 3 (ℓ "乀") ∷
   rw 99 q25 ∷
   rw⁻ 100 q5 ∷
   rw 101 q26 ∷
   re 102 1 (ℓ "乏丹乏") ∷
   rw 104 q1 ∷
   re 98 5 (ℓ "中") ∷
   re 100 1 (ℓ "乏丼丠丼乏") ∷
   rw 99 q3 ∷
   re 100 3 (ℓ "乀") ∷
   rw 100 q25 ∷
   rw⁻ 101 q5 ∷
   rw 102 q26 ∷
   re 103 1 (ℓ "乏丹乏") ∷
   rw 105 q1 ∷
   re 99 5 (ℓ "中") ∷
   re 101 1 (ℓ "乏丼丠丼乏") ∷
   rw 100 q3 ∷
   re 101 3 (ℓ "乀") ∷
   rw 101 q25 ∷
   rw⁻ 102 q5 ∷
   rw 103 q26 ∷
   re 104 1 (ℓ "乏丹乏") ∷
   rw 106 q1 ∷
   re 100 5 (ℓ "中") ∷
   re 102 1 (ℓ "乏丼丠丼乏") ∷
   rw 101 q3 ∷
   re 102 3 (ℓ "乀") ∷
   rw 102 q25 ∷
   rw⁻ 103 q5 ∷
   rw 104 q26 ∷
   re 105 1 (ℓ "乏丹乏") ∷
   rw 107 q1 ∷
   re 101 5 (ℓ "中") ∷
   re 103 1 (ℓ "乏丼丠丼乏") ∷
   rw 102 q3 ∷
   re 103 3 (ℓ "乀") ∷
   rw 103 q25 ∷
   rw⁻ 104 q5 ∷
   rw 105 q26 ∷
   re 106 1 (ℓ "乏丹乏") ∷
   rw 108 q1 ∷
   re 102 5 (ℓ "中") ∷
   re 104 1 (ℓ "乏丼临丼乏") ∷
   rw 103 q3 ∷
   re 104 3 (ℓ "乀") ∷
   rw 104 q25 ∷
   rw⁻ 105 q10 ∷
   rw 106 q26 ∷
   re 107 1 (ℓ "乏丹乏") ∷
   rw 109 q1 ∷
   re 103 5 (ℓ "乑") ∷
   rw 104 q27 ∷
   re 106 1 (ℓ "乏丼丠丼乏") ∷
   rw 105 q3 ∷
   re 106 3 (ℓ "乀") ∷
   rw 106 q25 ∷
   rw⁻ 107 q5 ∷
   rw 108 q26 ∷
   re 109 1 (ℓ "乏丹乏") ∷
   rw 111 q1 ∷
   re 105 5 (ℓ "中") ∷
   re 107 1 (ℓ "乏丼丠丼乏") ∷
   rw 106 q3 ∷
   re 107 3 (ℓ "乀") ∷
   rw 107 q25 ∷
   rw⁻ 108 q5 ∷
   rw 109 q26 ∷
   re 110 1 (ℓ "乏丹乏") ∷
   rw 112 q1 ∷
   re 106 5 (ℓ "中") ∷
   re 108 1 (ℓ "乏丼丠丼乏") ∷
   rw 107 q3 ∷
   re 108 3 (ℓ "乀") ∷
   rw 108 q25 ∷
   rw⁻ 109 q5 ∷
   rw 110 q26 ∷
   re 111 1 (ℓ "乏丹乏") ∷
   rw 113 q1 ∷
   re 107 5 (ℓ "中") ∷
   re 109 1 (ℓ "乏丼丠丼乏") ∷
   rw 108 q3 ∷
   re 109 3 (ℓ "乀") ∷
   rw 109 q25 ∷
   rw⁻ 110 q5 ∷
   rw 111 q26 ∷
   re 112 1 (ℓ "乏丹乏") ∷
   rw 114 q1 ∷
   re 108 5 (ℓ "中") ∷
   re 110 1 (ℓ "乏丼丠丼乏") ∷
   rw 109 q3 ∷
   re 110 3 (ℓ "乀") ∷
   rw 110 q25 ∷
   rw⁻ 111 q5 ∷
   rw 112 q26 ∷
   re 113 1 (ℓ "乏丹乏") ∷
   rw 115 q1 ∷
   re 109 5 (ℓ "中") ∷
   re 111 1 (ℓ "乏丼丠丼乏") ∷
   rw 110 q3 ∷
   re 111 3 (ℓ "乀") ∷
   rw 111 q25 ∷
   rw⁻ 112 q5 ∷
   rw 113 q26 ∷ []) Eq.refl
