{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D339 (W : Ws) where

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
  q1 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = wE 140 W
  q4 : Eqn
  q4 = wE 960 W
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 142 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 1 W
  q10 : Eqn
  q10 = wE 36 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 37 W
  q13 : Eqn
  q13 = wE 3 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part1: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part1 : ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄中中中中中中中中中中中中中中中並乏丶乏丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽並丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中中中中中中中中中中中中中中乏丼丠乌丼乏中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part1 = derive (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄中中中中中中中中中中中中中中中並乏丶乏丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽並丒乀丒中中中中中中乑业中中中中中中中中中") (ℓ "丒丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中中中中中中中中中中中中中中乏丼丠乌丼乏中中中中中中中业业业乑业中中中中中中中中中中中中中中中中中中丧丧乄丧乄乄丒乀丒中中中中中中乑业中中中中中中中中中")
  (re 67 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷
   re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q1 ∷
   rw 65 q2 ∷
   rw⁻ 64 q1 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q1 ∷
   rw 64 q2 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q1 ∷
   rw 63 q2 ∷
   rw⁻ 62 q1 ∷
   re 63 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q1 ∷
   rw 62 q2 ∷
   rw⁻ 61 q1 ∷
   re 62 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q1 ∷
   rw 61 q2 ∷
   rw⁻ 60 q1 ∷
   re 61 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q1 ∷
   rw 60 q2 ∷
   rw⁻ 59 q1 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q1 ∷
   rw 59 q2 ∷
   rw⁻ 58 q1 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q1 ∷
   rw 58 q2 ∷
   rw⁻ 57 q1 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q1 ∷
   rw 57 q2 ∷
   rw⁻ 56 q1 ∷
   re 57 3 (ℓ "丽") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q1 ∷
   rw 56 q2 ∷
   rw⁻ 55 q1 ∷
   re 56 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q1 ∷
   rw 55 q2 ∷
   rw⁻ 54 q1 ∷
   re 55 3 (ℓ "丽") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q1 ∷
   rw 54 q2 ∷
   rw⁻ 53 q1 ∷
   re 54 3 (ℓ "丽") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q1 ∷
   rw 53 q2 ∷
   rw⁻ 52 q1 ∷
   re 53 3 (ℓ "丽") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q1 ∷
   rw 52 q2 ∷
   rw⁻ 51 q1 ∷
   re 52 3 (ℓ "丽") ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q2 ∷
   rw 47 q3 ∷
   rw 46 q2 ∷
   rw 45 q2 ∷
   rw 46 q4 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q1 ∷
   rw 46 q5 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q1 ∷
   rw 47 q5 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q1 ∷
   rw 48 q5 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q1 ∷
   rw 49 q5 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q1 ∷
   rw 50 q5 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q1 ∷
   rw 51 q5 ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q1 ∷
   rw 52 q5 ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q1 ∷
   rw 53 q5 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q1 ∷
   rw 54 q5 ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q1 ∷
   rw 55 q5 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q1 ∷
   rw 56 q5 ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q1 ∷
   rw 57 q5 ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q1 ∷
   rw 58 q5 ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q1 ∷
   rw 59 q5 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q1 ∷
   rw 60 q5 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "中") ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q1 ∷
   rw 61 q5 ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q1 ∷
   rw 62 q5 ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q1 ∷
   rw 63 q5 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q1 ∷
   rw 64 q5 ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q1 ∷
   rw 65 q5 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q1 ∷
   rw 66 q5 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q1 ∷
   rw 67 q5 ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q1 ∷
   rw 68 q5 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q1 ∷
   rw 69 q5 ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丶乏") ∷
   rw 69 q1 ∷
   rw 70 q5 ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q1 ∷
   rw 71 q5 ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q1 ∷
   rw 72 q5 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q6 ∷
   rw 73 q6 ∷
   rw 74 q6 ∷
   re 76 1 (ℓ "乏乇乏") ∷
   rw 75 q1 ∷
   rw 76 q7 ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "乑") ∷
   rw 76 q6 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q1 ∷
   rw 78 q5 ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q1 ∷
   rw 79 q5 ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q1 ∷
   rw 80 q5 ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q1 ∷
   rw 81 q5 ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q1 ∷
   rw 82 q5 ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q1 ∷
   rw 83 q5 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q1 ∷
   rw 84 q5 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q1 ∷
   rw 85 q5 ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q1 ∷
   rw 86 q5 ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q1 ∷
   rw 87 q5 ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q1 ∷
   rw 88 q5 ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "中") ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q1 ∷
   rw 89 q5 ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "中") ∷
   re 90 1 (ℓ "乏丶乏") ∷
   rw 89 q1 ∷
   rw 90 q5 ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "中") ∷
   re 91 1 (ℓ "乏丶乏") ∷
   rw 90 q1 ∷
   rw 91 q5 ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "中") ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q1 ∷
   rw 92 q5 ∷
   rw 93 q1 ∷
   re 91 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q1 ∷
   rw 93 q5 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏丶乏") ∷
   rw 93 q1 ∷
   rw 94 q5 ∷
   rw 95 q1 ∷
   re 93 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏丶乏") ∷
   rw 94 q1 ∷
   rw 95 q5 ∷
   rw 96 q1 ∷
   re 94 3 (ℓ "中") ∷
   rw 95 q5 ∷
   rw 96 q5 ∷
   rw 97 q7 ∷
   rw 98 q5 ∷
   rw 99 q7 ∷
   rw 100 q7 ∷
   rw 101 q8 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q9 ∷
   re 45 3 (ℓ "乀") ∷
   rw 45 q10 ∷
   rw⁻ 46 q11 ∷
   rw 47 q12 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 50 q13 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q9 ∷
   re 46 3 (ℓ "乀") ∷
   rw 46 q10 ∷
   rw⁻ 47 q11 ∷
   rw 48 q12 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 51 q13 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q9 ∷
   re 47 3 (ℓ "乀") ∷
   rw 47 q10 ∷
   rw⁻ 48 q11 ∷
   rw 49 q12 ∷
   re 50 1 (ℓ "乏丹乏") ∷
   rw 52 q13 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q9 ∷
   re 48 3 (ℓ "乀") ∷
   rw 48 q10 ∷
   rw⁻ 49 q11 ∷
   rw 50 q12 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 53 q13 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q9 ∷
   re 49 3 (ℓ "乀") ∷
   rw 49 q10 ∷
   rw⁻ 50 q11 ∷
   rw 51 q12 ∷
   re 52 1 (ℓ "乏丹乏") ∷
   rw 54 q13 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q9 ∷
   re 50 3 (ℓ "乀") ∷
   rw 50 q10 ∷
   rw⁻ 51 q11 ∷
   rw 52 q12 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 55 q13 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q9 ∷
   re 51 3 (ℓ "乀") ∷
   rw 51 q10 ∷
   rw⁻ 52 q11 ∷
   rw 53 q12 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 56 q13 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q9 ∷
   re 52 3 (ℓ "乀") ∷
   rw 52 q10 ∷
   rw⁻ 53 q11 ∷
   rw 54 q12 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 57 q13 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q9 ∷
   re 53 3 (ℓ "乀") ∷
   rw 53 q10 ∷
   rw⁻ 54 q11 ∷
   rw 55 q12 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 58 q13 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q9 ∷
   re 54 3 (ℓ "乀") ∷
   rw 54 q10 ∷
   rw⁻ 55 q11 ∷
   rw 56 q12 ∷
   re 57 1 (ℓ "乏丹乏") ∷
   rw 59 q13 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q9 ∷
   re 55 3 (ℓ "乀") ∷
   rw 55 q10 ∷
   rw⁻ 56 q11 ∷
   rw 57 q12 ∷
   re 58 1 (ℓ "乏丹乏") ∷
   rw 60 q13 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q9 ∷
   re 56 3 (ℓ "乀") ∷
   rw 56 q10 ∷
   rw⁻ 57 q11 ∷
   rw 58 q12 ∷
   re 59 1 (ℓ "乏丹乏") ∷
   rw 61 q13 ∷
   re 55 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q9 ∷
   re 57 3 (ℓ "乀") ∷
   rw 57 q10 ∷
   rw⁻ 58 q11 ∷
   rw 59 q12 ∷
   re 60 1 (ℓ "乏丹乏") ∷
   rw 62 q13 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q9 ∷
   re 58 3 (ℓ "乀") ∷
   rw 58 q10 ∷
   rw⁻ 59 q11 ∷
   rw 60 q12 ∷
   re 61 1 (ℓ "乏丹乏") ∷
   rw 63 q13 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q9 ∷
   re 59 3 (ℓ "乀") ∷
   rw 59 q10 ∷
   rw⁻ 60 q11 ∷
   rw 61 q12 ∷
   re 62 1 (ℓ "乏丹乏") ∷
   rw 64 q13 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q9 ∷
   re 60 3 (ℓ "乀") ∷
   rw 60 q10 ∷
   rw⁻ 61 q11 ∷
   rw 62 q12 ∷
   re 63 1 (ℓ "乏丹乏") ∷
   rw 65 q13 ∷
   re 59 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q9 ∷
   re 61 3 (ℓ "乀") ∷
   rw 61 q10 ∷
   rw⁻ 62 q11 ∷
   rw 63 q12 ∷
   re 64 1 (ℓ "乏丹乏") ∷
   rw 66 q13 ∷
   re 60 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q9 ∷
   re 62 3 (ℓ "乀") ∷
   rw 62 q10 ∷
   rw⁻ 63 q11 ∷
   rw 64 q12 ∷
   re 65 1 (ℓ "乏丹乏") ∷
   rw 67 q13 ∷
   re 61 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q9 ∷
   re 63 3 (ℓ "乀") ∷
   rw 63 q10 ∷
   rw⁻ 64 q11 ∷
   rw 65 q12 ∷
   re 66 1 (ℓ "乏丹乏") ∷
   rw 68 q13 ∷
   re 62 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q9 ∷
   re 64 3 (ℓ "乀") ∷
   rw 64 q10 ∷
   rw⁻ 65 q11 ∷ []) Eq.refl
