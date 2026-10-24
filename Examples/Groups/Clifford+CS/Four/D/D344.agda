{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D344 (W : Ws) where

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
  q3 = wE 36 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q5 : Eqn
  q5 = wE 37 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q10 : Eqn
  q10 = wE 140 W
  q11 : Eqn
  q11 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q12 : Eqn
  q12 = wE 964 W
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 142 W
  q15 : Eqn
  q15 = wE 31 W
  q16 : Eqn
  q16 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q17 : Eqn
  q17 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q18 : Eqn
  q18 = wE 464 W
  q19 : Eqn
  q19 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = wE 843 W
  q22 : Eqn
  q22 = wE 151 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part6: 451 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part6 : ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中乑业中中中中中乏丼丠丼乀乏中中中丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒中中中中中中乑业中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part6 = derive (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中乑业中中中中中乏丼丠丼乀乏中中中丧丧乄丧乄乄") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丒乀丒中中中中中中乑业中中中中中中中中中丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (re 114 1 (ℓ "乏丹乏") ∷
   rw 116 q1 ∷
   re 110 5 (ℓ "中") ∷
   re 112 1 (ℓ "乏丼丠丼乏") ∷
   rw 111 q2 ∷
   re 112 3 (ℓ "乀") ∷
   rw 112 q3 ∷
   rw⁻ 113 q4 ∷
   rw 114 q5 ∷
   re 115 1 (ℓ "乏丹乏") ∷
   rw 117 q1 ∷
   re 111 5 (ℓ "中") ∷
   re 113 1 (ℓ "乏丼丠丼乏") ∷
   rw 112 q2 ∷
   re 113 3 (ℓ "乀") ∷
   rw 113 q3 ∷
   rw⁻ 114 q4 ∷
   rw 115 q5 ∷
   re 116 1 (ℓ "乏丹乏") ∷
   rw 118 q1 ∷
   re 112 5 (ℓ "中") ∷
   re 114 1 (ℓ "乏丼丠丼乏") ∷
   rw 113 q2 ∷
   re 114 3 (ℓ "乀") ∷
   rw 114 q3 ∷
   rw⁻ 115 q4 ∷
   rw 116 q5 ∷
   re 117 1 (ℓ "乏丹乏") ∷
   rw 119 q1 ∷
   re 113 5 (ℓ "中") ∷
   rw 114 q6 ∷
   re 113 1 (ℓ "乏丧乏") ∷
   rw⁻ 115 q7 ∷
   rw 114 q8 ∷
   rw⁻ 113 q7 ∷
   re 114 3 (ℓ "丽") ∷
   re 112 1 (ℓ "乏丧乏") ∷
   rw⁻ 114 q7 ∷
   rw 113 q8 ∷
   rw⁻ 112 q7 ∷
   re 113 3 (ℓ "丽") ∷
   re 111 1 (ℓ "乏丧乏") ∷
   rw⁻ 113 q7 ∷
   rw 112 q8 ∷
   rw⁻ 111 q7 ∷
   re 112 3 (ℓ "丽") ∷
   re 110 1 (ℓ "乏丧乏") ∷
   rw⁻ 112 q7 ∷
   rw 111 q8 ∷
   rw⁻ 110 q7 ∷
   re 111 3 (ℓ "丽") ∷
   re 109 1 (ℓ "乏丧乏") ∷
   rw⁻ 111 q7 ∷
   rw 110 q8 ∷
   rw⁻ 109 q7 ∷
   re 110 3 (ℓ "丽") ∷
   re 108 1 (ℓ "乏丧乏") ∷
   rw⁻ 110 q7 ∷
   rw 109 q8 ∷
   rw⁻ 108 q7 ∷
   re 109 3 (ℓ "丽") ∷
   re 107 1 (ℓ "乏丧乏") ∷
   rw⁻ 109 q7 ∷
   rw 108 q8 ∷
   rw⁻ 107 q7 ∷
   re 108 3 (ℓ "丽") ∷
   re 106 1 (ℓ "乏丧乏") ∷
   rw⁻ 108 q7 ∷
   rw 107 q8 ∷
   rw⁻ 106 q7 ∷
   re 107 3 (ℓ "丽") ∷
   re 105 1 (ℓ "乏丧乏") ∷
   rw⁻ 107 q7 ∷
   rw 106 q8 ∷
   rw⁻ 105 q7 ∷
   re 106 3 (ℓ "丽") ∷
   rw⁻ 104 q9 ∷
   re 103 1 (ℓ "乏乄乏") ∷
   rw⁻ 105 q7 ∷
   rw 104 q10 ∷
   rw⁻ 103 q7 ∷
   re 104 3 (ℓ "乔") ∷
   re 102 1 (ℓ "乏丧乏") ∷
   rw⁻ 104 q7 ∷
   rw 103 q8 ∷
   rw⁻ 102 q7 ∷
   re 103 3 (ℓ "丽") ∷
   re 101 1 (ℓ "乏丧乏") ∷
   rw⁻ 103 q7 ∷
   rw 102 q8 ∷
   rw⁻ 101 q7 ∷
   re 102 3 (ℓ "丽") ∷
   re 100 1 (ℓ "乏丧乏") ∷
   rw⁻ 102 q7 ∷
   rw 101 q8 ∷
   rw⁻ 100 q7 ∷
   re 101 3 (ℓ "丽") ∷
   re 99 1 (ℓ "乏丧乏") ∷
   rw⁻ 101 q7 ∷
   rw 100 q8 ∷
   rw⁻ 99 q7 ∷
   re 100 3 (ℓ "丽") ∷
   re 98 1 (ℓ "乏丧乏") ∷
   rw⁻ 100 q7 ∷
   rw 99 q8 ∷
   rw⁻ 98 q7 ∷
   re 99 3 (ℓ "丽") ∷
   re 97 1 (ℓ "乏丧乏") ∷
   rw⁻ 99 q7 ∷
   rw 98 q8 ∷
   rw⁻ 97 q7 ∷
   re 98 3 (ℓ "丽") ∷
   rw 96 q8 ∷
   rw 95 q8 ∷
   rw 94 q8 ∷
   rw 93 q8 ∷
   rw 92 q8 ∷
   rw 91 q8 ∷
   rw⁻ 90 q11 ∷
   rw 89 q10 ∷
   rw 88 q8 ∷
   rw 87 q8 ∷
   rw 86 q8 ∷
   rw⁻ 85 q11 ∷
   rw 84 q10 ∷
   rw⁻ 83 q11 ∷
   rw 82 q10 ∷
   rw 83 q12 ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q7 ∷
   rw 83 q13 ∷
   rw 84 q7 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q7 ∷
   rw 84 q13 ∷
   rw 85 q7 ∷
   re 83 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q7 ∷
   rw 85 q13 ∷
   rw 86 q7 ∷
   re 84 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q7 ∷
   rw 86 q13 ∷
   rw 87 q7 ∷
   re 85 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q7 ∷
   rw 87 q13 ∷
   rw 88 q7 ∷
   re 86 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q7 ∷
   rw 88 q13 ∷
   rw 89 q7 ∷
   re 87 3 (ℓ "中") ∷
   re 89 1 (ℓ "乏乇乏") ∷
   rw 88 q7 ∷
   rw 89 q14 ∷
   rw 90 q7 ∷
   re 88 3 (ℓ "乑") ∷
   rw 89 q9 ∷
   re 91 1 (ℓ "乏丶乏") ∷
   rw 90 q7 ∷
   rw 91 q13 ∷
   rw 92 q7 ∷
   re 90 3 (ℓ "中") ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q7 ∷
   rw 92 q13 ∷
   rw 93 q7 ∷
   re 91 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q7 ∷
   rw 93 q13 ∷
   rw 94 q7 ∷
   re 92 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏丶乏") ∷
   rw 93 q7 ∷
   rw 94 q13 ∷
   rw 95 q7 ∷
   re 93 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏丶乏") ∷
   rw 94 q7 ∷
   rw 95 q13 ∷
   rw 96 q7 ∷
   re 94 3 (ℓ "中") ∷
   re 96 1 (ℓ "乏丶乏") ∷
   rw 95 q7 ∷
   rw 96 q13 ∷
   rw 97 q7 ∷
   re 95 3 (ℓ "中") ∷
   re 97 1 (ℓ "乏丶乏") ∷
   rw 96 q7 ∷
   rw 97 q13 ∷
   rw 98 q7 ∷
   re 96 3 (ℓ "中") ∷
   re 98 1 (ℓ "乏丶乏") ∷
   rw 97 q7 ∷
   rw 98 q13 ∷
   rw 99 q7 ∷
   re 97 3 (ℓ "中") ∷
   re 99 1 (ℓ "乏丶乏") ∷
   rw 98 q7 ∷
   rw 99 q13 ∷
   rw 100 q7 ∷
   re 98 3 (ℓ "中") ∷
   rw 99 q14 ∷
   rw 100 q11 ∷
   rw 101 q14 ∷
   rw 102 q11 ∷
   rw 103 q13 ∷
   rw 104 q13 ∷
   rw 105 q13 ∷
   rw 106 q14 ∷
   rw 107 q11 ∷
   rw 108 q13 ∷
   rw 109 q13 ∷
   rw 110 q13 ∷
   rw 111 q13 ∷
   rw 112 q13 ∷
   rw 113 q13 ∷
   rw 114 q15 ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q2 ∷
   re 82 3 (ℓ "乀") ∷
   rw 82 q3 ∷
   rw⁻ 83 q4 ∷
   rw 84 q5 ∷
   re 85 1 (ℓ "乏丹乏") ∷
   rw 87 q1 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q2 ∷
   re 83 3 (ℓ "乀") ∷
   rw 83 q3 ∷
   rw⁻ 84 q4 ∷
   rw 85 q5 ∷
   re 86 1 (ℓ "乏丹乏") ∷
   rw 88 q1 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q2 ∷
   re 84 3 (ℓ "乀") ∷
   rw 84 q3 ∷
   rw⁻ 85 q4 ∷
   rw 86 q5 ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 89 q1 ∷
   re 83 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q2 ∷
   re 85 3 (ℓ "乀") ∷
   rw 85 q3 ∷
   rw⁻ 86 q4 ∷
   rw 87 q5 ∷
   re 88 1 (ℓ "乏丹乏") ∷
   rw 90 q1 ∷
   re 84 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q2 ∷
   re 86 3 (ℓ "乀") ∷
   rw 86 q3 ∷
   rw⁻ 87 q4 ∷
   rw 88 q5 ∷
   re 89 1 (ℓ "乏丹乏") ∷
   rw 91 q1 ∷
   re 85 5 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q2 ∷
   re 87 3 (ℓ "乀") ∷
   rw 87 q3 ∷
   rw⁻ 88 q4 ∷
   rw 89 q5 ∷
   re 90 1 (ℓ "乏丹乏") ∷
   rw 92 q1 ∷
   re 86 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼临丼乏") ∷
   rw 87 q2 ∷
   re 88 3 (ℓ "乀") ∷
   rw 88 q3 ∷
   rw⁻ 89 q16 ∷
   rw 90 q5 ∷
   re 91 1 (ℓ "乏丹乏") ∷
   rw 93 q1 ∷
   re 87 5 (ℓ "乑") ∷
   rw 88 q17 ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q2 ∷
   re 90 3 (ℓ "乀") ∷
   rw 90 q3 ∷
   rw⁻ 91 q4 ∷
   rw 92 q5 ∷
   re 93 1 (ℓ "乏丹乏") ∷
   rw 95 q1 ∷
   re 89 5 (ℓ "中") ∷
   re 91 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q2 ∷
   re 91 3 (ℓ "乀") ∷
   rw 91 q3 ∷
   rw⁻ 92 q4 ∷
   rw 93 q5 ∷
   re 94 1 (ℓ "乏丹乏") ∷
   rw 96 q1 ∷
   re 90 5 (ℓ "中") ∷
   re 92 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q2 ∷
   re 92 3 (ℓ "乀") ∷
   rw 92 q3 ∷
   rw⁻ 93 q4 ∷
   rw 94 q5 ∷
   re 95 1 (ℓ "乏丹乏") ∷
   rw 97 q1 ∷
   re 91 5 (ℓ "中") ∷
   re 93 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q2 ∷
   re 93 3 (ℓ "乀") ∷
   rw 93 q3 ∷
   rw⁻ 94 q4 ∷
   rw 95 q5 ∷
   re 96 1 (ℓ "乏丹乏") ∷
   rw 98 q1 ∷
   re 92 5 (ℓ "中") ∷
   re 94 1 (ℓ "乏丼丠丼乏") ∷
   rw 93 q2 ∷
   re 94 3 (ℓ "乀") ∷
   rw 94 q3 ∷
   rw⁻ 95 q4 ∷
   rw 96 q5 ∷
   re 97 1 (ℓ "乏丹乏") ∷
   rw 99 q1 ∷
   re 93 5 (ℓ "中") ∷
   re 95 1 (ℓ "乏丼丠丼乏") ∷
   rw 94 q2 ∷
   re 95 3 (ℓ "乀") ∷
   rw 95 q3 ∷
   rw⁻ 96 q4 ∷
   rw 97 q5 ∷
   re 98 1 (ℓ "乏丹乏") ∷
   rw 100 q1 ∷
   re 94 5 (ℓ "中") ∷
   re 96 1 (ℓ "乏丼丠丼乏") ∷
   rw 95 q2 ∷
   re 96 3 (ℓ "乀") ∷
   rw 96 q3 ∷
   rw⁻ 97 q4 ∷
   rw 98 q5 ∷
   re 99 1 (ℓ "乏丹乏") ∷
   rw 101 q1 ∷
   re 95 5 (ℓ "中") ∷
   re 97 1 (ℓ "乏丼丠丼乏") ∷
   rw 96 q2 ∷
   re 97 3 (ℓ "乀") ∷
   rw 97 q3 ∷
   rw⁻ 98 q4 ∷
   rw 99 q5 ∷
   re 100 1 (ℓ "乏丹乏") ∷
   rw 102 q1 ∷
   re 96 5 (ℓ "中") ∷
   re 98 1 (ℓ "乏丼丠丼乏") ∷
   rw 97 q2 ∷
   re 98 3 (ℓ "乀") ∷
   rw 98 q3 ∷
   rw⁻ 99 q4 ∷
   rw 100 q5 ∷
   re 101 1 (ℓ "乏丹乏") ∷
   rw 103 q1 ∷
   re 97 5 (ℓ "中") ∷
   rw 98 q2 ∷
   re 97 1 (ℓ "乏丧乏") ∷
   rw 99 q1 ∷
   re 96 1 (ℓ "乏丧乏") ∷
   rw 98 q1 ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q1 ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q1 ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw 95 q1 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q1 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q1 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 92 q1 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q1 ∷
   rw 88 q18 ∷
   re 87 1 (ℓ "乏乄乏") ∷
   rw 89 q1 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q1 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q1 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q1 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q1 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q1 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q1 ∷
   rw 80 q19 ∷
   rw 79 q19 ∷
   rw 78 q20 ∷
   rw 77 q19 ∷
   rw 76 q20 ∷
   rw 75 q20 ∷
   rw 76 q21 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "中") ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "中") ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q2 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q2 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q22 ∷
   rw 85 q2 ∷
   re 83 3 (ℓ "中") ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "中") ∷
   rw 87 q2 ∷
   re 85 3 (ℓ "中") ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "中") ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "中") ∷
   rw 90 q2 ∷
   re 88 3 (ℓ "中") ∷
   rw 91 q2 ∷
   re 89 3 (ℓ "中") ∷
   rw 92 q2 ∷
   re 90 3 (ℓ "中") ∷
   rw 93 q2 ∷
   re 91 3 (ℓ "中") ∷
   rw⁻ 92 q20 ∷
   rw⁻ 93 q20 ∷
   rw⁻ 94 q19 ∷
   rw⁻ 95 q20 ∷
   rw⁻ 96 q19 ∷
   rw⁻ 97 q19 ∷
   rw 98 q1 ∷ []) Eq.refl
