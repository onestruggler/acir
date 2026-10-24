{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D347 (W : Ws) where

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
  q3 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q6 : Eqn
  q6 = wE 965 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 142 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 1 W
  q11 : Eqn
  q11 = wE 36 W
  q12 : Eqn
  q12 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q13 : Eqn
  q13 = wE 37 W
  q14 : Eqn
  q14 = wE 3 W
  q15 : Eqn
  q15 = eqn (ℓ "丹业") (ℓ "业丹") (low₃-comm ((CX₀₁ ↑)) (S))
  q16 : Eqn
  q16 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0) part2: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part2 : ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中中中中中中中中中中中中中业业业乑业中中中中中並乏丶乏丽丽丽业业业乔业业业业乔业並丹丧丧乄丧乄乄丒乀丒乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中业业业乑业乏丼丠丼乀乏中中中中中中中中业业业乑业业业业乑业乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part2 = derive (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧中中中中中中中中中中中中中中中中中中业业业乑业中中中中中並乏丶乏丽丽丽业业业乔业业业业乔业並丹丧丧乄丧乄乄丒乀丒乑业乑业中中中乑业中中中中中中") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临中中中中中中中中中中中中中中中中中中业业业乑业乏丼丠丼乀乏中中中中中中中中业业业乑业业业业乑业乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒乀丒乑业乑业中中中乑业中中中中中中")
  (re 71 3 (ℓ "丽") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q1 ∷
   rw 70 q2 ∷
   rw⁻ 69 q1 ∷
   re 70 3 (ℓ "丽") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q1 ∷
   rw 69 q2 ∷
   rw⁻ 68 q1 ∷
   re 69 3 (ℓ "丽") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q1 ∷
   rw 68 q2 ∷
   rw⁻ 67 q1 ∷
   re 68 3 (ℓ "丽") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q1 ∷
   rw 67 q2 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q1 ∷
   rw 66 q2 ∷
   rw⁻ 65 q1 ∷
   re 66 3 (ℓ "丽") ∷
   rw⁻ 64 q3 ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw⁻ 65 q1 ∷
   rw 64 q4 ∷
   rw⁻ 63 q1 ∷
   re 64 3 (ℓ "乔") ∷
   rw⁻ 62 q3 ∷
   rw⁻ 61 q3 ∷
   rw⁻ 60 q3 ∷
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
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q1 ∷
   rw 51 q2 ∷
   rw⁻ 50 q1 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q1 ∷
   rw 50 q2 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (ℓ "丽") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q1 ∷
   rw 49 q2 ∷
   rw⁻ 48 q1 ∷
   re 49 3 (ℓ "丽") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q1 ∷
   rw 48 q2 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (ℓ "丽") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q1 ∷
   rw 47 q2 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (ℓ "丽") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q1 ∷
   rw 46 q2 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (ℓ "丽") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q1 ∷
   rw 45 q2 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (ℓ "丽") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (ℓ "丽") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q1 ∷
   rw 43 q2 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (ℓ "丽") ∷
   rw 41 q2 ∷
   rw 40 q2 ∷
   rw 39 q2 ∷
   rw 38 q2 ∷
   rw 37 q2 ∷
   rw 36 q2 ∷
   rw⁻ 35 q5 ∷
   rw 34 q4 ∷
   rw 33 q2 ∷
   rw 32 q2 ∷
   rw 31 q2 ∷
   rw⁻ 30 q5 ∷
   rw 29 q4 ∷
   rw⁻ 28 q5 ∷
   rw 27 q4 ∷
   rw 28 q6 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q1 ∷
   rw 28 q7 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q1 ∷
   rw 29 q7 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q1 ∷
   rw 30 q7 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q1 ∷
   rw 31 q7 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q1 ∷
   rw 32 q7 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q1 ∷
   rw 33 q7 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q1 ∷
   rw 34 q7 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q1 ∷
   rw 35 q7 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q1 ∷
   rw 36 q7 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q1 ∷
   rw 37 q7 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q1 ∷
   rw 38 q7 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q1 ∷
   rw 39 q7 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q1 ∷
   rw 40 q7 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q1 ∷
   rw 41 q7 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q1 ∷
   rw 42 q7 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q1 ∷
   rw 43 q7 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q1 ∷
   rw 44 q7 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q1 ∷
   rw 45 q7 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q3 ∷
   rw 46 q3 ∷
   rw 47 q3 ∷
   re 49 1 (ℓ "乏乇乏") ∷
   rw 48 q1 ∷
   rw 49 q8 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乑") ∷
   rw 49 q3 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q1 ∷
   rw 51 q7 ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q1 ∷
   rw 52 q7 ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q1 ∷
   rw 53 q7 ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q1 ∷
   rw 54 q7 ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q1 ∷
   rw 55 q7 ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q1 ∷
   rw 56 q7 ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q1 ∷
   rw 57 q7 ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q1 ∷
   rw 58 q7 ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q1 ∷
   rw 59 q7 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q3 ∷
   rw 60 q3 ∷
   rw 61 q3 ∷
   re 63 1 (ℓ "乏乇乏") ∷
   rw 62 q1 ∷
   rw 63 q8 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q3 ∷
   rw 64 q3 ∷
   rw 65 q3 ∷
   rw 66 q3 ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q1 ∷
   rw 68 q8 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q3 ∷
   rw 69 q8 ∷
   rw 70 q5 ∷
   rw 71 q8 ∷
   rw 72 q5 ∷
   rw 73 q7 ∷
   rw 74 q7 ∷
   rw 75 q7 ∷
   rw 76 q8 ∷
   rw 77 q5 ∷
   rw 78 q7 ∷
   rw 79 q7 ∷
   rw 80 q7 ∷
   rw 81 q7 ∷
   rw 82 q7 ∷
   rw 83 q7 ∷
   rw 84 q9 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q10 ∷
   re 27 3 (ℓ "乀") ∷
   rw 27 q11 ∷
   rw⁻ 28 q12 ∷
   rw 29 q13 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q14 ∷
   re 26 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q10 ∷
   re 28 3 (ℓ "乀") ∷
   rw 28 q11 ∷
   rw⁻ 29 q12 ∷
   rw 30 q13 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 33 q14 ∷
   re 27 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q10 ∷
   re 29 3 (ℓ "乀") ∷
   rw 29 q11 ∷
   rw⁻ 30 q12 ∷
   rw 31 q13 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 34 q14 ∷
   re 28 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q10 ∷
   re 30 3 (ℓ "乀") ∷
   rw 30 q11 ∷
   rw⁻ 31 q12 ∷
   rw 32 q13 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q14 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q10 ∷
   re 31 3 (ℓ "乀") ∷
   rw 31 q11 ∷
   rw⁻ 32 q12 ∷
   rw 33 q13 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 36 q14 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q10 ∷
   re 32 3 (ℓ "乀") ∷
   rw 32 q11 ∷
   rw⁻ 33 q12 ∷
   rw 34 q13 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 37 q14 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q10 ∷
   re 33 3 (ℓ "乀") ∷
   rw 33 q11 ∷
   rw⁻ 34 q12 ∷
   rw 35 q13 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 38 q14 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q10 ∷
   re 34 3 (ℓ "乀") ∷
   rw 34 q11 ∷
   rw⁻ 35 q12 ∷
   rw 36 q13 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 39 q14 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q10 ∷
   re 35 3 (ℓ "乀") ∷
   rw 35 q11 ∷
   rw⁻ 36 q12 ∷
   rw 37 q13 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q14 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q10 ∷
   re 36 3 (ℓ "乀") ∷
   rw 36 q11 ∷
   rw⁻ 37 q12 ∷
   rw 38 q13 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 41 q14 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q10 ∷
   re 37 3 (ℓ "乀") ∷
   rw 37 q11 ∷
   rw⁻ 38 q12 ∷
   rw 39 q13 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 42 q14 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q10 ∷
   re 38 3 (ℓ "乀") ∷
   rw 38 q11 ∷
   rw⁻ 39 q12 ∷
   rw 40 q13 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 43 q14 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q10 ∷
   re 39 3 (ℓ "乀") ∷
   rw 39 q11 ∷
   rw⁻ 40 q12 ∷
   rw 41 q13 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 44 q14 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q10 ∷
   re 40 3 (ℓ "乀") ∷
   rw 40 q11 ∷
   rw⁻ 41 q12 ∷
   rw 42 q13 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 45 q14 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q10 ∷
   re 41 3 (ℓ "乀") ∷
   rw 41 q11 ∷
   rw⁻ 42 q12 ∷
   rw 43 q13 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 46 q14 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q10 ∷
   re 42 3 (ℓ "乀") ∷
   rw 42 q11 ∷
   rw⁻ 43 q12 ∷
   rw 44 q13 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 47 q14 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q10 ∷
   re 43 3 (ℓ "乀") ∷
   rw 43 q11 ∷
   rw⁻ 44 q12 ∷
   rw 45 q13 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 48 q14 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q10 ∷
   re 44 3 (ℓ "乀") ∷
   rw 44 q11 ∷
   rw⁻ 45 q12 ∷
   rw 46 q13 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 49 q14 ∷
   re 43 5 (ℓ "中") ∷
   rw 44 q15 ∷
   rw 45 q15 ∷
   rw 46 q15 ∷
   re 48 1 (ℓ "乏丼临丼乏") ∷
   rw 47 q10 ∷
   re 48 3 (ℓ "乀") ∷
   rw 48 q11 ∷
   rw⁻ 49 q16 ∷
   rw 50 q13 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 53 q14 ∷
   re 47 5 (ℓ "乑") ∷
   rw 48 q15 ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q10 ∷
   re 50 3 (ℓ "乀") ∷
   rw 50 q11 ∷
   rw⁻ 51 q12 ∷
   rw 52 q13 ∷ []) Eq.refl
