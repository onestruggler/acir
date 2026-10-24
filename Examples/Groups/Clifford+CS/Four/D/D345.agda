{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D345 (W : Ws) where

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
  q1 = wE 878 W
  q2 : Eqn
  q2 = wE 879 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 157 W
  q5 : Eqn
  q5 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q6 : Eqn
  q6 = wE 158 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 880 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 956 W
  q11 : Eqn
  q11 = eqn (ℓ "丒且") (ℓ "且丒") (low-comm ((X ↑)) (S))
  q12 : Eqn
  q12 = wE 625 W
  q13 : Eqn
  q13 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q14 : Eqn
  q14 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = wE 882 W
  q17 : Eqn
  q17 = wE 5 W
  q18 : Eqn
  q18 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 7 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,3->0) part0: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part0 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丒乀丒乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乏丧乏並丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业並丒乀丒乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~13-⟶0⟩-part0 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丒乀丒乑业乑业中中中乑业中中中中中中") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒乀丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乏丧乏並丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业並丒乀丒乑业乑业中中中乑业中中中中中中")
  (rw 0 q1 ∷
   rw 45 q2 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 46 q3 ∷
   re 47 3 (ℓ "乑") ∷
   re 47 1 (ℓ "乏丼临丼乏") ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "乀") ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   rw 48 q6 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 47 q7 ∷
   re 48 5 (ℓ "乑") ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw 50 q7 ∷
   re 46 3 (ℓ "乀") ∷
   rw 47 q2 ∷
   rw 44 q2 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q3 ∷
   re 46 3 (ℓ "乑") ∷
   re 46 1 (ℓ "乏丼临丼乏") ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "乀") ∷
   rw 49 q4 ∷
   rw 48 q5 ∷
   rw 47 q6 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 46 q7 ∷
   re 47 5 (ℓ "乑") ∷
   re 47 1 (ℓ "乏乄乏") ∷
   rw 49 q7 ∷
   re 45 3 (ℓ "乀") ∷
   rw 46 q2 ∷
   rw 43 q8 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q3 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q3 ∷
   re 49 3 (ℓ "乀") ∷
   rw 48 q4 ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q7 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q7 ∷
   re 44 3 (ℓ "乀") ∷
   rw 45 q8 ∷
   rw 42 q2 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q3 ∷
   re 44 3 (ℓ "乑") ∷
   re 44 1 (ℓ "乏丼临丼乏") ∷
   rw 50 q3 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q4 ∷
   rw 46 q5 ∷
   rw 45 q6 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q7 ∷
   re 45 5 (ℓ "乑") ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw 47 q7 ∷
   re 43 3 (ℓ "乀") ∷
   rw 44 q2 ∷
   rw 41 q8 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q3 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q3 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q4 ∷
   rw 45 q9 ∷
   rw 44 q6 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q7 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q7 ∷
   re 42 3 (ℓ "乀") ∷
   rw 43 q8 ∷
   rw 40 q8 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q3 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q3 ∷
   re 46 3 (ℓ "乀") ∷
   rw 45 q4 ∷
   rw 44 q9 ∷
   rw 43 q6 ∷
   re 43 1 (ℓ "乏丹乏") ∷
   rw 42 q7 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q7 ∷
   re 41 3 (ℓ "乀") ∷
   rw 42 q8 ∷
   rw 39 q10 ∷
   rw 38 q8 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q3 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q3 ∷
   re 44 3 (ℓ "乀") ∷
   rw 43 q4 ∷
   rw 42 q9 ∷
   rw 41 q6 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q7 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q7 ∷
   re 39 3 (ℓ "乀") ∷
   rw 40 q8 ∷
   rw 37 q8 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q3 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q3 ∷
   re 43 3 (ℓ "乀") ∷
   rw 42 q4 ∷
   rw 41 q9 ∷
   rw 40 q6 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q7 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q7 ∷
   re 38 3 (ℓ "乀") ∷
   rw 39 q8 ∷
   rw 36 q8 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q3 ∷
   re 38 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q3 ∷
   re 42 3 (ℓ "乀") ∷
   rw 41 q4 ∷
   rw 40 q9 ∷
   rw 39 q6 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q7 ∷
   re 39 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q7 ∷
   re 37 3 (ℓ "乀") ∷
   rw 38 q8 ∷
   rw 35 q8 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q3 ∷
   re 37 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "乀") ∷
   rw 40 q4 ∷
   rw 39 q9 ∷
   rw 38 q6 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q7 ∷
   re 38 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q7 ∷
   re 36 3 (ℓ "乀") ∷
   rw 37 q8 ∷
   rw 34 q8 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q3 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q4 ∷
   rw 38 q9 ∷
   rw 37 q6 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q7 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q7 ∷
   re 35 3 (ℓ "乀") ∷
   rw 36 q8 ∷
   rw 33 q8 ∷
   re 35 1 (ℓ "乏丹乏") ∷
   rw 34 q3 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "乀") ∷
   rw 38 q4 ∷
   rw 37 q9 ∷
   rw 36 q6 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q7 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q7 ∷
   re 34 3 (ℓ "乀") ∷
   rw 35 q8 ∷
   rw⁻ 32 q11 ∷
   rw 33 q12 ∷
   rw⁻ 34 q11 ∷
   rw 31 q2 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q3 ∷
   re 33 3 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丼临丼乏") ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "乀") ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   rw 34 q6 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q7 ∷
   re 34 5 (ℓ "乑") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q7 ∷
   re 32 3 (ℓ "乀") ∷
   rw 33 q2 ∷
   rw 30 q8 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q3 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "乀") ∷
   rw 35 q4 ∷
   rw 34 q9 ∷
   rw 33 q6 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 32 q7 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q7 ∷
   re 31 3 (ℓ "乀") ∷
   rw 32 q8 ∷
   rw 29 q8 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q3 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "乀") ∷
   rw 34 q4 ∷
   rw 33 q9 ∷
   rw 32 q6 ∷
   re 32 1 (ℓ "乏丹乏") ∷
   rw 31 q7 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q7 ∷
   re 30 3 (ℓ "乀") ∷
   rw 31 q8 ∷
   rw 28 q8 ∷
   re 30 1 (ℓ "乏丹乏") ∷
   rw 29 q3 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "乀") ∷
   rw 33 q4 ∷
   rw 32 q9 ∷
   rw 31 q6 ∷
   re 31 1 (ℓ "乏丹乏") ∷
   rw 30 q7 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q7 ∷
   re 29 3 (ℓ "乀") ∷
   rw 30 q8 ∷
   rw⁻ 27 q11 ∷
   rw 28 q12 ∷
   rw⁻ 29 q11 ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 27 q3 ∷
   re 28 3 (ℓ "乑") ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "乀") ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q6 ∷
   re 29 1 (ℓ "乏丹乏") ∷
   rw 28 q7 ∷
   re 29 5 (ℓ "乑") ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q7 ∷
   re 27 3 (ℓ "乀") ∷
   rw 28 q2 ∷
   rw⁻ 25 q11 ∷
   rw 26 q12 ∷
   rw⁻ 27 q11 ∷
   rw 24 q2 ∷
   re 26 1 (ℓ "乏丹乏") ∷
   rw 25 q3 ∷
   re 26 3 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼临丼乏") ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "乀") ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   re 27 1 (ℓ "乏丹乏") ∷
   rw 26 q7 ∷
   re 27 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q7 ∷
   re 25 3 (ℓ "乀") ∷
   rw 26 q2 ∷
   rw 23 q10 ∷
   rw 26 q3 ∷
   rw 25 q13 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q7 ∷
   rw 23 q13 ∷
   rw 22 q14 ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   rw 19 q14 ∷
   rw 18 q15 ∷
   rw 17 q15 ∷
   rw 18 q16 ∷
   rw⁻ 17 q13 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "乀") ∷
   rw⁻ 19 q13 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 23 q15 ∷
   rw⁻ 24 q14 ∷
   rw⁻ 25 q14 ∷
   rw 26 q7 ∷
   rw 91 q17 ∷
   rw⁻ 90 q18 ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw⁻ 91 q19 ∷
   rw 90 q20 ∷
   rw⁻ 89 q19 ∷
   re 90 3 (ℓ "乔") ∷
   rw⁻ 88 q18 ∷
   rw⁻ 87 q18 ∷
   rw⁻ 86 q18 ∷
   rw⁻ 85 q18 ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw⁻ 86 q19 ∷
   rw 85 q20 ∷
   rw⁻ 84 q19 ∷
   re 85 3 (ℓ "乔") ∷
   rw⁻ 83 q18 ∷
   rw⁻ 82 q18 ∷
   rw⁻ 81 q18 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q19 ∷
   rw 81 q21 ∷
   rw⁻ 80 q19 ∷
   re 81 3 (ℓ "丽") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q19 ∷
   rw 80 q21 ∷
   rw⁻ 79 q19 ∷
   re 80 3 (ℓ "丽") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q19 ∷
   rw 79 q21 ∷
   rw⁻ 78 q19 ∷
   re 79 3 (ℓ "丽") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q19 ∷
   rw 78 q21 ∷
   rw⁻ 77 q19 ∷
   re 78 3 (ℓ "丽") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q19 ∷
   rw 77 q21 ∷
   rw⁻ 76 q19 ∷
   re 77 3 (ℓ "丽") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q19 ∷
   rw 76 q21 ∷
   rw⁻ 75 q19 ∷
   re 76 3 (ℓ "丽") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q19 ∷
   rw 75 q21 ∷
   rw⁻ 74 q19 ∷
   re 75 3 (ℓ "丽") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q19 ∷
   rw 74 q21 ∷
   rw⁻ 73 q19 ∷
   re 74 3 (ℓ "丽") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q19 ∷
   rw 73 q21 ∷
   rw⁻ 72 q19 ∷
   re 73 3 (ℓ "丽") ∷
   rw⁻ 71 q18 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw⁻ 72 q19 ∷
   rw 71 q20 ∷
   rw⁻ 70 q19 ∷
   re 71 3 (ℓ "乔") ∷
   rw⁻ 69 q18 ∷
   rw⁻ 68 q18 ∷
   rw⁻ 67 q18 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q19 ∷
   rw 67 q21 ∷
   rw⁻ 66 q19 ∷
   re 67 3 (ℓ "丽") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q19 ∷
   rw 66 q21 ∷
   rw⁻ 65 q19 ∷
   re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q19 ∷
   rw 65 q21 ∷
   rw⁻ 64 q19 ∷
   re 65 3 (ℓ "丽") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q19 ∷
   rw 64 q21 ∷
   rw⁻ 63 q19 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q19 ∷
   rw 63 q21 ∷
   rw⁻ 62 q19 ∷
   re 63 3 (ℓ "丽") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q19 ∷
   rw 62 q21 ∷
   rw⁻ 61 q19 ∷
   re 62 3 (ℓ "丽") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw⁻ 62 q19 ∷
   rw 61 q21 ∷
   rw⁻ 60 q19 ∷
   re 61 3 (ℓ "丽") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw⁻ 61 q19 ∷
   rw 60 q21 ∷
   rw⁻ 59 q19 ∷
   re 60 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q19 ∷
   rw 59 q21 ∷
   rw⁻ 58 q19 ∷
   re 59 3 (ℓ "丽") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q19 ∷
   rw 58 q21 ∷
   rw⁻ 57 q19 ∷
   re 58 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q19 ∷
   rw 57 q21 ∷
   rw⁻ 56 q19 ∷
   re 57 3 (ℓ "丽") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q19 ∷
   rw 56 q21 ∷
   rw⁻ 55 q19 ∷
   re 56 3 (ℓ "丽") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q19 ∷
   rw 55 q21 ∷
   rw⁻ 54 q19 ∷
   re 55 3 (ℓ "丽") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q19 ∷
   rw 54 q21 ∷
   rw⁻ 53 q19 ∷
   re 54 3 (ℓ "丽") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q19 ∷
   rw 53 q21 ∷
   rw⁻ 52 q19 ∷
   re 53 3 (ℓ "丽") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q19 ∷
   rw 52 q21 ∷
   rw⁻ 51 q19 ∷
   re 52 3 (ℓ "丽") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q19 ∷
   rw 51 q21 ∷
   rw⁻ 50 q19 ∷
   re 51 3 (ℓ "丽") ∷
   re 49 1 (ℓ "乏丧乏") ∷ []) Eq.refl
