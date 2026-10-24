{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D461 (W : Ws) where

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
  q3 = wE 142 W
  q4 : Eqn
  q4 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = wE 36 W
  q7 : Eqn
  q7 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 37 W
  q9 : Eqn
  q9 = wE 883 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q11 : Eqn
  q11 = wE 665 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q14 : Eqn
  q14 = wE 3 W
  q15 : Eqn
  q15 = wE 880 W
  q16 : Eqn
  q16 = wE 157 W
  q17 : Eqn
  q17 = wE 158 W
  q18 : Eqn
  q18 = wE 879 W
  q19 : Eqn
  q19 = wE 881 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part2: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 : ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒丠丠丠临丠丠乀乄且乄且丧丧丧乄且丧丧丧丧丧丧乏並丶乏丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽並乀中中中乑中中丒丹丒丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠丠临丠丠乀中中中中中中乑业中乏丧丒乏丹丒中中中中中中中乀中中中乑中中丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 = derive (ℓ "丒丠丠临丠临临丒丒丹丒丠丠丠临丠丠乀乄且乄且丧丧丧乄且丧丧丧丧丧丧乏並丶乏丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽並乀中中中乑中中丒丹丒丧丧乄丧乄乄") (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠丠临丠丠乀中中中中中中乑业中乏丧丒乏丹丒中中中中中中中乀中中中乑中中丧丧乄丧乄乄")
  (rw 34 q1 ∷
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
   re 40 1 (ℓ "乏乇乏") ∷
   rw 39 q2 ∷
   rw 40 q3 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "乑") ∷
   rw 40 q4 ∷
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
   rw 50 q5 ∷
   re 18 1 (ℓ "丼临丼") ∷
   rw 17 q6 ∷
   rw⁻ 18 q7 ∷
   rw 19 q8 ∷
   re 17 3 (ℓ "乄") ∷
   rw 18 q9 ∷
   re 20 1 (ℓ "丼临丼") ∷
   rw 19 q6 ∷
   rw⁻ 20 q7 ∷
   rw 21 q8 ∷
   re 19 3 (ℓ "乄") ∷
   rw 20 q9 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q6 ∷
   rw⁻ 22 q10 ∷
   rw 23 q8 ∷
   re 21 3 (ℓ "丧") ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q6 ∷
   rw⁻ 23 q10 ∷
   rw 24 q8 ∷
   re 22 3 (ℓ "丧") ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q6 ∷
   rw⁻ 24 q10 ∷
   rw 25 q8 ∷
   re 23 3 (ℓ "丧") ∷
   re 25 1 (ℓ "丼临丼") ∷
   rw 24 q6 ∷
   rw⁻ 25 q7 ∷
   rw 26 q8 ∷
   re 24 3 (ℓ "乄") ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q6 ∷
   rw⁻ 27 q10 ∷
   rw 28 q8 ∷
   re 26 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q6 ∷
   rw⁻ 28 q10 ∷
   rw 29 q8 ∷
   re 27 3 (ℓ "丧") ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q6 ∷
   rw⁻ 29 q10 ∷
   rw 30 q8 ∷
   re 28 3 (ℓ "丧") ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q6 ∷
   rw⁻ 30 q10 ∷
   rw 31 q8 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q6 ∷
   rw⁻ 31 q10 ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q6 ∷
   rw⁻ 32 q10 ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "丧") ∷
   rw 11 q11 ∷
   rw 58 q12 ∷
   rw 57 q13 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q14 ∷
   rw 57 q15 ∷
   rw⁻ 56 q13 ∷
   rw 59 q12 ∷
   re 57 3 (ℓ "中") ∷
   rw 58 q14 ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q12 ∷
   re 61 3 (ℓ "乀") ∷
   rw 60 q16 ∷
   rw 59 q10 ∷
   rw 58 q17 ∷
   re 58 1 (ℓ "乏丹乏") ∷
   rw 57 q14 ∷
   re 58 5 (ℓ "中") ∷
   rw 60 q12 ∷
   rw 59 q13 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q14 ∷
   rw 59 q15 ∷
   rw⁻ 58 q13 ∷
   rw 61 q12 ∷
   re 59 3 (ℓ "中") ∷
   rw 60 q14 ∷
   rw 57 q12 ∷
   rw 56 q13 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q14 ∷
   rw 56 q15 ∷
   rw⁻ 55 q13 ∷
   rw 58 q12 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q14 ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q12 ∷
   re 60 3 (ℓ "乀") ∷
   rw 59 q16 ∷
   rw 58 q10 ∷
   rw 57 q17 ∷
   re 57 1 (ℓ "乏丹乏") ∷
   rw 56 q14 ∷
   re 57 5 (ℓ "中") ∷
   rw 59 q12 ∷
   rw 58 q13 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q14 ∷
   rw 58 q15 ∷
   rw⁻ 57 q13 ∷
   rw 60 q12 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q14 ∷
   rw 56 q12 ∷
   rw 55 q13 ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw 56 q14 ∷
   rw 55 q18 ∷
   rw⁻ 54 q13 ∷
   rw 57 q12 ∷
   re 55 3 (ℓ "乑") ∷
   rw 56 q14 ∷
   re 55 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q12 ∷
   re 59 3 (ℓ "乀") ∷
   rw 58 q16 ∷
   rw 57 q7 ∷
   rw 56 q17 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 55 q14 ∷
   re 56 5 (ℓ "乑") ∷
   rw 58 q12 ∷
   rw 57 q13 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q14 ∷
   rw 57 q18 ∷
   rw⁻ 56 q13 ∷
   rw 59 q12 ∷
   re 57 3 (ℓ "乑") ∷
   rw 58 q14 ∷
   rw 55 q12 ∷
   rw 54 q13 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q14 ∷
   rw 54 q15 ∷
   rw⁻ 53 q13 ∷
   rw 56 q12 ∷
   re 54 3 (ℓ "中") ∷
   rw 55 q14 ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q12 ∷
   re 58 3 (ℓ "乀") ∷
   rw 57 q16 ∷
   rw 56 q10 ∷
   rw 55 q17 ∷
   re 55 1 (ℓ "乏丹乏") ∷
   rw 54 q14 ∷
   re 55 5 (ℓ "中") ∷
   rw 57 q12 ∷
   rw 56 q13 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q14 ∷
   rw 56 q15 ∷
   rw⁻ 55 q13 ∷
   rw 58 q12 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q14 ∷
   rw 54 q12 ∷
   rw 53 q13 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q14 ∷
   rw 53 q15 ∷
   rw⁻ 52 q13 ∷
   rw 55 q12 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q14 ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q12 ∷
   re 57 3 (ℓ "乀") ∷
   rw 56 q16 ∷
   rw 55 q10 ∷
   rw 54 q17 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 53 q14 ∷
   re 54 5 (ℓ "中") ∷
   rw 56 q12 ∷
   rw 55 q13 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q14 ∷
   rw 55 q15 ∷
   rw⁻ 54 q13 ∷
   rw 57 q12 ∷
   re 55 3 (ℓ "中") ∷
   rw 56 q14 ∷
   rw 53 q12 ∷
   rw 52 q13 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q14 ∷
   rw 52 q15 ∷
   rw⁻ 51 q13 ∷
   rw 54 q12 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q14 ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q12 ∷
   re 56 3 (ℓ "乀") ∷
   rw 55 q16 ∷
   rw 54 q10 ∷
   rw 53 q17 ∷
   re 53 1 (ℓ "乏丹乏") ∷
   rw 52 q14 ∷
   re 53 5 (ℓ "中") ∷
   rw 55 q12 ∷
   rw 54 q13 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q14 ∷
   rw 54 q15 ∷
   rw⁻ 53 q13 ∷
   rw 56 q12 ∷
   re 54 3 (ℓ "中") ∷
   rw 55 q14 ∷
   rw 50 q19 ∷
   rw 51 q12 ∷
   rw 50 q13 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q14 ∷
   rw 50 q15 ∷
   rw⁻ 49 q13 ∷
   rw 52 q12 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q14 ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q12 ∷
   re 54 3 (ℓ "乀") ∷
   rw 53 q16 ∷
   rw 52 q10 ∷
   rw 51 q17 ∷
   re 51 1 (ℓ "乏丹乏") ∷
   rw 50 q14 ∷
   re 51 5 (ℓ "中") ∷
   rw 53 q12 ∷
   rw 52 q13 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q14 ∷
   rw 52 q15 ∷
   rw⁻ 51 q13 ∷
   rw 54 q12 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q14 ∷
   rw 50 q12 ∷
   rw 49 q13 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   rw⁻ 48 q13 ∷
   rw 51 q12 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q14 ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q12 ∷
   re 53 3 (ℓ "乀") ∷
   rw 52 q16 ∷
   rw 51 q10 ∷
   rw 50 q17 ∷
   re 50 1 (ℓ "乏丹乏") ∷
   rw 49 q14 ∷
   re 50 5 (ℓ "中") ∷
   rw 52 q12 ∷
   rw 51 q13 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q14 ∷
   rw 51 q15 ∷
   rw⁻ 50 q13 ∷
   rw 53 q12 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q14 ∷
   rw 49 q12 ∷
   rw 48 q13 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q14 ∷
   rw 48 q15 ∷
   rw⁻ 47 q13 ∷
   rw 50 q12 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q14 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q12 ∷
   re 52 3 (ℓ "乀") ∷
   rw 51 q16 ∷
   rw 50 q10 ∷
   rw 49 q17 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 48 q14 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q12 ∷
   rw 50 q13 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q14 ∷
   rw 50 q15 ∷
   rw⁻ 49 q13 ∷
   rw 52 q12 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q14 ∷
   rw 48 q12 ∷
   rw 47 q13 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q14 ∷
   rw 47 q15 ∷
   rw⁻ 46 q13 ∷
   rw 49 q12 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q14 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q12 ∷
   re 51 3 (ℓ "乀") ∷
   rw 50 q16 ∷
   rw 49 q10 ∷
   rw 48 q17 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 47 q14 ∷
   re 48 5 (ℓ "中") ∷
   rw 50 q12 ∷
   rw 49 q13 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   rw⁻ 48 q13 ∷
   rw 51 q12 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q14 ∷
   rw 47 q12 ∷
   rw 46 q13 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q14 ∷
   rw 46 q15 ∷
   rw⁻ 45 q13 ∷
   rw 48 q12 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q14 ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q12 ∷
   re 50 3 (ℓ "乀") ∷
   rw 49 q16 ∷
   rw 48 q10 ∷
   rw 47 q17 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 46 q14 ∷
   re 47 5 (ℓ "中") ∷
   rw 49 q12 ∷
   rw 48 q13 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q14 ∷
   rw 48 q15 ∷
   rw⁻ 47 q13 ∷
   rw 50 q12 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q14 ∷
   rw 46 q12 ∷
   rw 45 q13 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q14 ∷
   rw 45 q15 ∷
   rw⁻ 44 q13 ∷
   rw 47 q12 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q14 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q12 ∷
   re 49 3 (ℓ "乀") ∷
   rw 48 q16 ∷
   rw 47 q10 ∷
   rw 46 q17 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q14 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q12 ∷
   rw 47 q13 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q14 ∷
   rw 47 q15 ∷
   rw⁻ 46 q13 ∷
   rw 49 q12 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q14 ∷
   rw 45 q12 ∷
   rw 44 q13 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q14 ∷
   rw 44 q15 ∷
   rw⁻ 43 q13 ∷
   rw 46 q12 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q14 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q12 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q16 ∷
   rw 46 q10 ∷
   rw 45 q17 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q14 ∷
   re 45 5 (ℓ "中") ∷
   rw 47 q12 ∷
   rw 46 q13 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q14 ∷
   rw 46 q15 ∷
   rw⁻ 45 q13 ∷
   rw 48 q12 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q14 ∷
   rw 44 q12 ∷
   rw 43 q13 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q14 ∷ []) Eq.refl
