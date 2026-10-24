{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D341 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 142 W
  q5 : Eqn
  q5 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 36 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 37 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q13 : Eqn
  q13 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part3: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part3 : ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹中乏並丶乏丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业丹乏丼丠丼乏中中中中中中中中中中中中中中中中中乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part3 = derive (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹中乏並丶乏丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽乇且乇且丶丶丶乇且丶丶丶丶丶丶並丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中中中中中中中中中中业业业乑业丹乏丼丠丼乏中中中中中中中中中中中中中中中中中乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中")
  (rw 31 q1 ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q2 ∷
   rw 32 q1 ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q2 ∷
   rw 33 q1 ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q2 ∷
   rw 34 q1 ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q2 ∷
   rw 35 q1 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q2 ∷
   rw 36 q1 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q2 ∷
   rw 37 q1 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q2 ∷
   rw 38 q1 ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q2 ∷
   rw 39 q1 ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q2 ∷
   rw 40 q1 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q2 ∷
   rw 41 q1 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q2 ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q2 ∷
   rw 43 q1 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q2 ∷
   rw 44 q1 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q2 ∷
   rw 45 q1 ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q2 ∷
   rw 46 q1 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q2 ∷
   rw 47 q1 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q2 ∷
   rw 48 q1 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q2 ∷
   rw 49 q1 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q2 ∷
   rw 50 q1 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q2 ∷
   rw 51 q1 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q2 ∷
   rw 52 q1 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q2 ∷
   rw 53 q1 ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q2 ∷
   rw 54 q1 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q2 ∷
   rw 55 q1 ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q2 ∷
   rw 56 q1 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "中") ∷
   rw 56 q3 ∷
   rw 57 q3 ∷
   rw 58 q3 ∷
   re 60 1 (ℓ "乏乇乏") ∷
   rw 59 q2 ∷
   rw 60 q4 ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "乑") ∷
   rw 60 q3 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q2 ∷
   rw 62 q1 ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q2 ∷
   rw 63 q1 ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q2 ∷
   rw 64 q1 ∷
   rw 65 q2 ∷
   re 63 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q2 ∷
   rw 65 q1 ∷
   rw 66 q2 ∷
   re 64 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q2 ∷
   rw 66 q1 ∷
   rw 67 q2 ∷
   re 65 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q2 ∷
   rw 67 q1 ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q2 ∷
   rw 68 q1 ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q2 ∷
   rw 69 q1 ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q2 ∷
   rw 70 q1 ∷
   rw 71 q2 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q2 ∷
   rw 71 q1 ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q2 ∷
   rw 72 q1 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q2 ∷
   rw 73 q1 ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q2 ∷
   rw 74 q1 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q2 ∷
   rw 75 q1 ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q2 ∷
   rw 76 q1 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q2 ∷
   rw 77 q1 ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q2 ∷
   rw 78 q1 ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q2 ∷
   rw 79 q1 ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "中") ∷
   rw 79 q4 ∷
   rw 80 q5 ∷
   rw 81 q4 ∷
   rw 82 q5 ∷
   rw 83 q1 ∷
   rw 84 q1 ∷
   rw 85 q1 ∷
   rw 86 q4 ∷
   rw 87 q5 ∷
   rw 88 q1 ∷
   rw 89 q1 ∷
   rw 90 q1 ∷
   rw 91 q1 ∷
   rw 92 q1 ∷
   rw 93 q1 ∷
   rw 94 q6 ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q7 ∷
   re 29 3 (ℓ "乀") ∷
   rw 29 q8 ∷
   rw⁻ 30 q9 ∷
   rw 31 q10 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 34 q11 ∷
   re 28 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q7 ∷
   re 30 3 (ℓ "乀") ∷
   rw 30 q8 ∷
   rw⁻ 31 q9 ∷
   rw 32 q10 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q11 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q7 ∷
   re 31 3 (ℓ "乀") ∷
   rw 31 q8 ∷
   rw⁻ 32 q9 ∷
   rw 33 q10 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 36 q11 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q7 ∷
   re 32 3 (ℓ "乀") ∷
   rw 32 q8 ∷
   rw⁻ 33 q9 ∷
   rw 34 q10 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 37 q11 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q7 ∷
   re 33 3 (ℓ "乀") ∷
   rw 33 q8 ∷
   rw⁻ 34 q9 ∷
   rw 35 q10 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 38 q11 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q7 ∷
   re 34 3 (ℓ "乀") ∷
   rw 34 q8 ∷
   rw⁻ 35 q9 ∷
   rw 36 q10 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q11 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q7 ∷
   re 35 3 (ℓ "乀") ∷
   rw 35 q8 ∷
   rw⁻ 36 q9 ∷
   rw 37 q10 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q11 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q7 ∷
   re 36 3 (ℓ "乀") ∷
   rw 36 q8 ∷
   rw⁻ 37 q9 ∷
   rw 38 q10 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 41 q11 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q7 ∷
   re 37 3 (ℓ "乀") ∷
   rw 37 q8 ∷
   rw⁻ 38 q9 ∷
   rw 39 q10 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 42 q11 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q7 ∷
   re 38 3 (ℓ "乀") ∷
   rw 38 q8 ∷
   rw⁻ 39 q9 ∷
   rw 40 q10 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 43 q11 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q7 ∷
   re 39 3 (ℓ "乀") ∷
   rw 39 q8 ∷
   rw⁻ 40 q9 ∷
   rw 41 q10 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 44 q11 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q7 ∷
   re 40 3 (ℓ "乀") ∷
   rw 40 q8 ∷
   rw⁻ 41 q9 ∷
   rw 42 q10 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 45 q11 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q7 ∷
   re 41 3 (ℓ "乀") ∷
   rw 41 q8 ∷
   rw⁻ 42 q9 ∷
   rw 43 q10 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 46 q11 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q7 ∷
   re 42 3 (ℓ "乀") ∷
   rw 42 q8 ∷
   rw⁻ 43 q9 ∷
   rw 44 q10 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 47 q11 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q7 ∷
   re 43 3 (ℓ "乀") ∷
   rw 43 q8 ∷
   rw⁻ 44 q9 ∷
   rw 45 q10 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 48 q11 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q7 ∷
   re 44 3 (ℓ "乀") ∷
   rw 44 q8 ∷
   rw⁻ 45 q9 ∷
   rw 46 q10 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 49 q11 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q7 ∷
   re 45 3 (ℓ "乀") ∷
   rw 45 q8 ∷
   rw⁻ 46 q9 ∷
   rw 47 q10 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 50 q11 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q7 ∷
   re 46 3 (ℓ "乀") ∷
   rw 46 q8 ∷
   rw⁻ 47 q9 ∷
   rw 48 q10 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 51 q11 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q7 ∷
   re 47 3 (ℓ "乀") ∷
   rw 47 q8 ∷
   rw⁻ 48 q9 ∷
   rw 49 q10 ∷
   re 50 1 (ℓ "乏丹乏") ∷
   rw 52 q11 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q7 ∷
   re 48 3 (ℓ "乀") ∷
   rw 48 q8 ∷
   rw⁻ 49 q9 ∷
   rw 50 q10 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 53 q11 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q7 ∷
   re 49 3 (ℓ "乀") ∷
   rw 49 q8 ∷
   rw⁻ 50 q9 ∷
   rw 51 q10 ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 54 q11 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q7 ∷
   re 50 3 (ℓ "乀") ∷
   rw 50 q8 ∷
   rw⁻ 51 q9 ∷
   rw 52 q10 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 55 q11 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q7 ∷
   re 51 3 (ℓ "乀") ∷
   rw 51 q8 ∷
   rw⁻ 52 q9 ∷
   rw 53 q10 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 56 q11 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q7 ∷
   re 52 3 (ℓ "乀") ∷
   rw 52 q8 ∷
   rw⁻ 53 q9 ∷
   rw 54 q10 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 57 q11 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q7 ∷
   re 53 3 (ℓ "乀") ∷
   rw 53 q8 ∷
   rw⁻ 54 q9 ∷
   rw 55 q10 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 58 q11 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q7 ∷
   re 54 3 (ℓ "乀") ∷
   rw 54 q8 ∷
   rw⁻ 55 q9 ∷
   rw 56 q10 ∷
   re 57 1 (ℓ "乏丹乏") ∷
   rw 59 q11 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q7 ∷
   re 55 3 (ℓ "乀") ∷
   rw 55 q8 ∷
   rw⁻ 56 q9 ∷
   rw 57 q10 ∷
   re 58 1 (ℓ "乏丹乏") ∷
   rw 60 q11 ∷
   re 54 5 (ℓ "中") ∷
   rw 55 q12 ∷
   rw 56 q12 ∷
   rw 57 q12 ∷
   re 59 1 (ℓ "乏丼临丼乏") ∷
   rw 58 q7 ∷
   re 59 3 (ℓ "乀") ∷
   rw 59 q8 ∷
   rw⁻ 60 q13 ∷
   rw 61 q10 ∷
   re 62 1 (ℓ "乏丹乏") ∷
   rw 64 q11 ∷
   re 58 5 (ℓ "乑") ∷
   rw 59 q12 ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷ []) Eq.refl
