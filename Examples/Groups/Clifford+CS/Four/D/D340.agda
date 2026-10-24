{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D340 (W : Ws) where

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
  q1 = wE 37 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 36 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q7 : Eqn
  q7 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q14 : Eqn
  q14 = wE 961 W
  q15 : Eqn
  q15 = wE 27 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part2: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part2 : ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中中中中中中中中中中中中中中乏丼丠乌丼乏中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹中乏並丶乏丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part2 = derive (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中中中中中中中中中中中中中中乏丼丠乌丼乏中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹中乏並丶乏丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中")
  (rw 66 q1 ∷
   re 67 1 (ℓ "乏丹乏") ∷
   rw 69 q2 ∷
   re 63 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q3 ∷
   re 65 3 (ℓ "乀") ∷
   rw 65 q4 ∷
   rw⁻ 66 q5 ∷
   rw 67 q1 ∷
   re 68 1 (ℓ "乏丹乏") ∷
   rw 70 q2 ∷
   re 64 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q3 ∷
   re 66 3 (ℓ "乀") ∷
   rw 66 q4 ∷
   rw⁻ 67 q5 ∷
   rw 68 q1 ∷
   re 69 1 (ℓ "乏丹乏") ∷
   rw 71 q2 ∷
   re 65 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q3 ∷
   re 67 3 (ℓ "乀") ∷
   rw 67 q4 ∷
   rw⁻ 68 q5 ∷
   rw 69 q1 ∷
   re 70 1 (ℓ "乏丹乏") ∷
   rw 72 q2 ∷
   re 66 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q3 ∷
   re 68 3 (ℓ "乀") ∷
   rw 68 q4 ∷
   rw⁻ 69 q5 ∷
   rw 70 q1 ∷
   re 71 1 (ℓ "乏丹乏") ∷
   rw 73 q2 ∷
   re 67 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q3 ∷
   re 69 3 (ℓ "乀") ∷
   rw 69 q4 ∷
   rw⁻ 70 q5 ∷
   rw 71 q1 ∷
   re 72 1 (ℓ "乏丹乏") ∷
   rw 74 q2 ∷
   re 68 5 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q3 ∷
   re 70 3 (ℓ "乀") ∷
   rw 70 q4 ∷
   rw⁻ 71 q5 ∷
   rw 72 q1 ∷
   re 73 1 (ℓ "乏丹乏") ∷
   rw 75 q2 ∷
   re 69 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q3 ∷
   re 71 3 (ℓ "乀") ∷
   rw 71 q4 ∷
   rw⁻ 72 q5 ∷
   rw 73 q1 ∷
   re 74 1 (ℓ "乏丹乏") ∷
   rw 76 q2 ∷
   re 70 5 (ℓ "中") ∷
   rw 71 q6 ∷
   rw 72 q6 ∷
   rw 73 q6 ∷
   re 75 1 (ℓ "乏丼临丼乏") ∷
   rw 74 q3 ∷
   re 75 3 (ℓ "乀") ∷
   rw 75 q4 ∷
   rw⁻ 76 q7 ∷
   rw 77 q1 ∷
   re 78 1 (ℓ "乏丹乏") ∷
   rw 80 q2 ∷
   re 74 5 (ℓ "乑") ∷
   rw 75 q6 ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q3 ∷
   re 77 3 (ℓ "乀") ∷
   rw 77 q4 ∷
   rw⁻ 78 q5 ∷
   rw 79 q1 ∷
   re 80 1 (ℓ "乏丹乏") ∷
   rw 82 q2 ∷
   re 76 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q3 ∷
   re 78 3 (ℓ "乀") ∷
   rw 78 q4 ∷
   rw⁻ 79 q5 ∷
   rw 80 q1 ∷
   re 81 1 (ℓ "乏丹乏") ∷
   rw 83 q2 ∷
   re 77 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q3 ∷
   re 79 3 (ℓ "乀") ∷
   rw 79 q4 ∷
   rw⁻ 80 q5 ∷
   rw 81 q1 ∷
   re 82 1 (ℓ "乏丹乏") ∷
   rw 84 q2 ∷
   re 78 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q3 ∷
   re 80 3 (ℓ "乀") ∷
   rw 80 q4 ∷
   rw⁻ 81 q5 ∷
   rw 82 q1 ∷
   re 83 1 (ℓ "乏丹乏") ∷
   rw 85 q2 ∷
   re 79 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q3 ∷
   re 81 3 (ℓ "乀") ∷
   rw 81 q4 ∷
   rw⁻ 82 q5 ∷
   rw 83 q1 ∷
   re 84 1 (ℓ "乏丹乏") ∷
   rw 86 q2 ∷
   re 80 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q3 ∷
   re 82 3 (ℓ "乀") ∷
   rw 82 q4 ∷
   rw⁻ 83 q5 ∷
   rw 84 q1 ∷
   re 85 1 (ℓ "乏丹乏") ∷
   rw 87 q2 ∷
   re 81 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q3 ∷
   re 83 3 (ℓ "乀") ∷
   rw 83 q4 ∷
   rw⁻ 84 q5 ∷
   rw 85 q1 ∷
   re 86 1 (ℓ "乏丹乏") ∷
   rw 88 q2 ∷
   re 82 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q3 ∷
   re 84 3 (ℓ "乀") ∷
   rw 84 q4 ∷
   rw⁻ 85 q5 ∷
   rw 86 q1 ∷
   re 87 1 (ℓ "乏丹乏") ∷
   rw 89 q2 ∷
   re 83 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q3 ∷
   re 85 3 (ℓ "乀") ∷
   rw 85 q4 ∷
   rw⁻ 86 q5 ∷
   rw 87 q1 ∷
   re 88 1 (ℓ "乏丹乏") ∷
   rw 90 q2 ∷
   re 84 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q3 ∷
   re 86 3 (ℓ "乀") ∷
   rw 86 q4 ∷
   rw⁻ 87 q5 ∷
   rw 88 q1 ∷
   re 89 1 (ℓ "乏丹乏") ∷
   rw 91 q2 ∷
   re 85 5 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q3 ∷
   re 87 3 (ℓ "乀") ∷
   rw 87 q4 ∷
   rw⁻ 88 q5 ∷
   rw 89 q1 ∷
   re 90 1 (ℓ "乏丹乏") ∷
   rw 92 q2 ∷
   re 86 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q3 ∷
   re 88 3 (ℓ "乀") ∷
   rw 88 q4 ∷
   rw⁻ 89 q5 ∷
   rw 90 q1 ∷
   re 91 1 (ℓ "乏丹乏") ∷
   rw 93 q2 ∷
   re 87 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q3 ∷
   re 89 3 (ℓ "乀") ∷
   rw 89 q4 ∷
   rw⁻ 90 q5 ∷
   rw 91 q1 ∷
   re 92 1 (ℓ "乏丹乏") ∷
   rw 94 q2 ∷
   re 88 5 (ℓ "中") ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q3 ∷
   re 90 3 (ℓ "乀") ∷
   rw 90 q4 ∷
   rw⁻ 91 q5 ∷
   rw 92 q1 ∷
   re 93 1 (ℓ "乏丹乏") ∷
   rw 95 q2 ∷
   re 89 5 (ℓ "中") ∷
   re 91 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q3 ∷
   re 91 3 (ℓ "乀") ∷
   rw 91 q4 ∷
   rw⁻ 92 q5 ∷
   rw 93 q1 ∷
   re 94 1 (ℓ "乏丹乏") ∷
   rw 96 q2 ∷
   re 90 5 (ℓ "中") ∷
   re 92 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q3 ∷
   re 92 3 (ℓ "乀") ∷
   rw 92 q4 ∷
   rw⁻ 93 q5 ∷
   rw 94 q1 ∷
   re 95 1 (ℓ "乏丹乏") ∷
   rw 97 q2 ∷
   re 91 5 (ℓ "中") ∷
   re 93 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q3 ∷
   re 93 3 (ℓ "乀") ∷
   rw 93 q4 ∷
   rw⁻ 94 q5 ∷
   rw 95 q1 ∷
   re 96 1 (ℓ "乏丹乏") ∷
   rw 98 q2 ∷
   re 92 5 (ℓ "中") ∷
   re 94 1 (ℓ "乏丼丠丼乏") ∷
   rw 93 q3 ∷
   re 94 3 (ℓ "乀") ∷
   rw 94 q4 ∷
   rw⁻ 95 q5 ∷
   rw 96 q1 ∷
   re 97 1 (ℓ "乏丹乏") ∷
   rw 99 q2 ∷
   re 93 5 (ℓ "中") ∷
   rw 94 q8 ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw⁻ 95 q9 ∷
   rw 94 q10 ∷
   rw⁻ 93 q9 ∷
   re 94 3 (ℓ "丽") ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw⁻ 94 q9 ∷
   rw 93 q10 ∷
   rw⁻ 92 q9 ∷
   re 93 3 (ℓ "丽") ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw⁻ 93 q9 ∷
   rw 92 q10 ∷
   rw⁻ 91 q9 ∷
   re 92 3 (ℓ "丽") ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw⁻ 92 q9 ∷
   rw 91 q10 ∷
   rw⁻ 90 q9 ∷
   re 91 3 (ℓ "丽") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw⁻ 91 q9 ∷
   rw 90 q10 ∷
   rw⁻ 89 q9 ∷
   re 90 3 (ℓ "丽") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw⁻ 90 q9 ∷
   rw 89 q10 ∷
   rw⁻ 88 q9 ∷
   re 89 3 (ℓ "丽") ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw⁻ 89 q9 ∷
   rw 88 q10 ∷
   rw⁻ 87 q9 ∷
   re 88 3 (ℓ "丽") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw⁻ 88 q9 ∷
   rw 87 q10 ∷
   rw⁻ 86 q9 ∷
   re 87 3 (ℓ "丽") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q9 ∷
   rw 86 q10 ∷
   rw⁻ 85 q9 ∷
   re 86 3 (ℓ "丽") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw⁻ 86 q9 ∷
   rw 85 q10 ∷
   rw⁻ 84 q9 ∷
   re 85 3 (ℓ "丽") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q9 ∷
   rw 84 q10 ∷
   rw⁻ 83 q9 ∷
   re 84 3 (ℓ "丽") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q9 ∷
   rw 83 q10 ∷
   rw⁻ 82 q9 ∷
   re 83 3 (ℓ "丽") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q9 ∷
   rw 82 q10 ∷
   rw⁻ 81 q9 ∷
   re 82 3 (ℓ "丽") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q9 ∷
   rw 81 q10 ∷
   rw⁻ 80 q9 ∷
   re 81 3 (ℓ "丽") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q9 ∷
   rw 80 q10 ∷
   rw⁻ 79 q9 ∷
   re 80 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q9 ∷
   rw 79 q10 ∷
   rw⁻ 78 q9 ∷
   re 79 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q9 ∷
   rw 78 q10 ∷
   rw⁻ 77 q9 ∷
   re 78 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q9 ∷
   rw 77 q10 ∷
   rw⁻ 76 q9 ∷
   re 77 3 (ℓ "丽") ∷
   rw⁻ 75 q11 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw⁻ 76 q9 ∷
   rw 75 q12 ∷
   rw⁻ 74 q9 ∷
   re 75 3 (ℓ "乔") ∷
   rw⁻ 73 q11 ∷
   rw⁻ 72 q11 ∷
   rw⁻ 71 q11 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q9 ∷
   rw 71 q10 ∷
   rw⁻ 70 q9 ∷
   re 71 3 (ℓ "丽") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q9 ∷
   rw 70 q10 ∷
   rw⁻ 69 q9 ∷
   re 70 3 (ℓ "丽") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q9 ∷
   rw 69 q10 ∷
   rw⁻ 68 q9 ∷
   re 69 3 (ℓ "丽") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q9 ∷
   rw 68 q10 ∷
   rw⁻ 67 q9 ∷
   re 68 3 (ℓ "丽") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q9 ∷
   rw 67 q10 ∷
   rw⁻ 66 q9 ∷
   re 67 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q9 ∷
   rw 66 q10 ∷
   rw⁻ 65 q9 ∷
   re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q9 ∷
   rw 65 q10 ∷
   rw⁻ 64 q9 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q9 ∷
   rw 64 q10 ∷
   rw⁻ 63 q9 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q9 ∷
   rw 63 q10 ∷
   rw⁻ 62 q9 ∷
   re 63 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q9 ∷
   rw 62 q10 ∷
   rw⁻ 61 q9 ∷
   re 62 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q9 ∷
   rw 61 q10 ∷
   rw⁻ 60 q9 ∷
   re 61 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q9 ∷
   rw 60 q10 ∷
   rw⁻ 59 q9 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q9 ∷
   rw 59 q10 ∷
   rw⁻ 58 q9 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q9 ∷
   rw 58 q10 ∷
   rw⁻ 57 q9 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q9 ∷
   rw 57 q10 ∷
   rw⁻ 56 q9 ∷
   re 57 3 (ℓ "丽") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q9 ∷
   rw 56 q10 ∷
   rw⁻ 55 q9 ∷
   re 56 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q9 ∷
   rw 55 q10 ∷
   rw⁻ 54 q9 ∷
   re 55 3 (ℓ "丽") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q9 ∷
   rw 54 q10 ∷
   rw⁻ 53 q9 ∷
   re 54 3 (ℓ "丽") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q9 ∷
   rw 53 q10 ∷
   rw⁻ 52 q9 ∷
   re 53 3 (ℓ "丽") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q9 ∷
   rw 52 q10 ∷
   rw⁻ 51 q9 ∷
   re 52 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q9 ∷
   rw 51 q10 ∷
   rw⁻ 50 q9 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q9 ∷
   rw 50 q10 ∷
   rw⁻ 49 q9 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q9 ∷
   rw 49 q10 ∷
   rw⁻ 48 q9 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q9 ∷
   rw 48 q10 ∷
   rw⁻ 47 q9 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q9 ∷
   rw 47 q10 ∷
   rw⁻ 46 q9 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q9 ∷
   rw 46 q10 ∷
   rw⁻ 45 q9 ∷
   re 46 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q9 ∷
   rw 45 q10 ∷
   rw⁻ 44 q9 ∷
   re 45 3 (ℓ "丽") ∷
   rw 43 q10 ∷
   rw 42 q10 ∷
   rw 41 q10 ∷
   rw 40 q10 ∷
   rw 39 q10 ∷
   rw 38 q10 ∷
   rw⁻ 37 q13 ∷
   rw 36 q12 ∷
   rw 35 q10 ∷
   rw 34 q10 ∷
   rw 33 q10 ∷
   rw⁻ 32 q13 ∷
   rw 31 q12 ∷
   rw⁻ 30 q13 ∷
   rw 29 q12 ∷
   rw 30 q14 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q9 ∷
   rw 30 q15 ∷
   rw 31 q9 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q9 ∷ []) Eq.refl
