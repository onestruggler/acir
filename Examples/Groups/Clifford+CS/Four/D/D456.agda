{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D456 (W : Ws) where

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
  q26 : Eqn
  q26 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q27 : Eqn
  q27 = wE 885 W
  q28 : Eqn
  q28 = wE 617 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part1: 500 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part1 : ⟪ (ℓ "丒丠丠临丠临临丒丠丠临丠临临乀乑业乑业中中丒乏乏丹丒中乑业中中中中中中乀中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑丒乏乄乏丹丒丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part1 = derive (ℓ "丒丠丠临丠临临丒丠丠临丠临临乀乑业乑业中中丒乏乏丹丒中乑业中中中中中中乀中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧丧丒丹丒丧丧乄丧乄乄") (ℓ "丒丠丠临丠临临丒丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑丒乏乄乏丹丒丧丧乄丧乄乄")
  (rw 21 q1 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q1 ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q2 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "乀") ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 21 q2 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q4 ∷
   rw 23 q1 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q1 ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q2 ∷
   rw 21 q4 ∷
   rw 20 q1 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   rw⁻ 19 q1 ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q2 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "乀") ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   re 21 1 (ℓ "乏丹乏") ∷
   rw 20 q2 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q4 ∷
   rw 22 q1 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q1 ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q2 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 19 q9 ∷
   rw⁻ 20 q8 ∷
   rw 19 q4 ∷
   rw 18 q1 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q2 ∷
   rw 18 q10 ∷
   rw⁻ 17 q1 ∷
   rw 20 q4 ∷
   re 18 3 (ℓ "乑") ∷
   rw 19 q2 ∷
   re 18 1 (ℓ "乏丼临丼乏") ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "乀") ∷
   rw 21 q5 ∷
   rw 20 q11 ∷
   rw 19 q7 ∷
   re 19 1 (ℓ "乏丹乏") ∷
   rw 18 q2 ∷
   re 19 5 (ℓ "乑") ∷
   rw 21 q4 ∷
   rw 20 q1 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q2 ∷
   rw 20 q10 ∷
   rw⁻ 19 q1 ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q2 ∷
   rw⁻ 16 q8 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 18 q8 ∷
   rw 17 q4 ∷
   rw 16 q1 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q2 ∷
   rw 16 q10 ∷
   rw⁻ 15 q1 ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q2 ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "乀") ∷
   rw 19 q5 ∷
   rw 18 q11 ∷
   rw 17 q7 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q2 ∷
   re 17 5 (ℓ "乑") ∷
   rw 19 q4 ∷
   rw 18 q1 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q2 ∷
   rw 18 q10 ∷
   rw⁻ 17 q1 ∷
   rw 20 q4 ∷
   re 18 3 (ℓ "乑") ∷
   rw 19 q2 ∷
   rw 14 q12 ∷
   rw 8 q13 ∷
   rw 55 q14 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q15 ∷
   rw 51 q15 ∷
   rw 50 q15 ∷
   rw 49 q15 ∷
   rw⁻ 48 q16 ∷
   rw 47 q17 ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw⁻ 43 q16 ∷
   rw 42 q17 ∷
   rw⁻ 41 q16 ∷
   rw 40 q17 ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw⁻ 41 q18 ∷
   rw 40 q17 ∷
   rw⁻ 39 q18 ∷
   re 40 3 (ℓ "乔") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw⁻ 40 q18 ∷
   rw 39 q17 ∷
   rw⁻ 38 q18 ∷
   re 39 3 (ℓ "乔") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q18 ∷
   rw 38 q15 ∷
   rw⁻ 37 q18 ∷
   re 38 3 (ℓ "丽") ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw⁻ 38 q18 ∷
   rw 37 q17 ∷
   rw⁻ 36 q18 ∷
   re 37 3 (ℓ "乔") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q18 ∷
   rw 36 q15 ∷
   rw⁻ 35 q18 ∷
   re 36 3 (ℓ "丽") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q18 ∷
   rw 35 q15 ∷
   rw⁻ 34 q18 ∷
   re 35 3 (ℓ "丽") ∷
   rw 35 q19 ∷
   rw 34 q20 ∷
   rw 35 q16 ∷
   rw 36 q20 ∷
   rw 37 q16 ∷
   rw 38 q21 ∷
   rw 39 q21 ∷
   rw 40 q21 ∷
   rw 41 q20 ∷
   rw 42 q16 ∷
   rw 43 q21 ∷
   rw 44 q21 ∷
   rw 45 q21 ∷
   rw 46 q21 ∷
   rw 47 q21 ∷
   rw 48 q21 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q18 ∷
   rw 50 q21 ∷
   rw 51 q18 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q18 ∷
   rw 51 q21 ∷
   rw 52 q18 ∷
   re 50 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏乇乏") ∷
   rw 51 q18 ∷
   rw 52 q20 ∷
   rw 53 q18 ∷
   re 51 3 (ℓ "乑") ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q18 ∷
   rw 53 q21 ∷
   rw 54 q18 ∷
   re 52 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏乇乏") ∷
   rw 53 q18 ∷
   rw 54 q20 ∷
   rw 55 q18 ∷
   re 53 3 (ℓ "乑") ∷
   re 55 1 (ℓ "乏乇乏") ∷
   rw 54 q18 ∷
   rw 55 q20 ∷
   rw 56 q18 ∷
   re 54 3 (ℓ "乑") ∷
   rw 55 q22 ∷
   re 34 1 (ℓ "丼临丼") ∷
   rw 33 q23 ∷
   rw⁻ 34 q11 ∷
   rw 35 q24 ∷
   re 33 3 (ℓ "乄") ∷
   rw 34 q25 ∷
   re 36 1 (ℓ "丼临丼") ∷
   rw 35 q23 ∷
   rw⁻ 36 q11 ∷
   rw 37 q24 ∷
   re 35 3 (ℓ "乄") ∷
   rw 36 q25 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q23 ∷
   rw⁻ 38 q6 ∷
   rw 39 q24 ∷
   re 37 3 (ℓ "丧") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q23 ∷
   rw⁻ 39 q6 ∷
   rw 40 q24 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q23 ∷
   rw⁻ 40 q6 ∷
   rw 41 q24 ∷
   re 39 3 (ℓ "丧") ∷
   re 41 1 (ℓ "丼临丼") ∷
   rw 40 q23 ∷
   rw⁻ 41 q11 ∷
   rw 42 q24 ∷
   re 40 3 (ℓ "乄") ∷
   rw 41 q25 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q23 ∷
   rw⁻ 43 q6 ∷
   rw 44 q24 ∷
   re 42 3 (ℓ "丧") ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q23 ∷
   rw⁻ 44 q6 ∷
   rw 45 q24 ∷
   re 43 3 (ℓ "丧") ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 44 q23 ∷
   rw⁻ 45 q6 ∷
   rw 46 q24 ∷
   re 44 3 (ℓ "丧") ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 45 q23 ∷
   rw⁻ 46 q6 ∷
   rw 47 q24 ∷
   re 45 3 (ℓ "丧") ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 46 q23 ∷
   rw⁻ 47 q6 ∷
   rw 48 q24 ∷
   re 46 3 (ℓ "丧") ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 47 q23 ∷
   rw⁻ 48 q6 ∷
   rw 49 q24 ∷
   re 47 3 (ℓ "丧") ∷
   rw 48 q14 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw⁻ 41 q16 ∷
   rw 40 q17 ∷
   rw 39 q15 ∷
   rw 38 q15 ∷
   rw 37 q15 ∷
   rw⁻ 36 q16 ∷
   rw 35 q17 ∷
   rw⁻ 34 q16 ∷
   rw 33 q17 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q18 ∷
   rw 33 q15 ∷
   rw⁻ 32 q18 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q18 ∷
   rw 32 q15 ∷
   rw⁻ 31 q18 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q18 ∷
   rw 31 q15 ∷
   rw⁻ 30 q18 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q18 ∷
   rw 30 q15 ∷
   rw⁻ 29 q18 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q18 ∷
   rw 29 q15 ∷
   rw⁻ 28 q18 ∷
   re 29 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q18 ∷
   rw 28 q15 ∷
   rw⁻ 27 q18 ∷
   re 28 3 (ℓ "丽") ∷
   rw⁻ 26 q26 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q18 ∷
   rw 26 q17 ∷
   rw⁻ 25 q18 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q18 ∷
   rw 25 q15 ∷
   rw⁻ 24 q18 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q18 ∷
   rw 24 q15 ∷
   rw⁻ 23 q18 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q18 ∷
   rw 23 q15 ∷
   rw⁻ 22 q18 ∷
   re 23 3 (ℓ "丽") ∷
   rw⁻ 21 q26 ∷
   re 20 1 (ℓ "乏乄乏") ∷
   rw⁻ 22 q18 ∷
   rw 21 q17 ∷
   rw⁻ 20 q18 ∷
   re 21 3 (ℓ "乔") ∷
   rw⁻ 19 q26 ∷
   re 18 1 (ℓ "乏乄乏") ∷
   rw⁻ 20 q18 ∷
   rw 19 q17 ∷
   rw⁻ 18 q18 ∷
   re 19 3 (ℓ "乔") ∷
   rw 19 q27 ∷
   rw 18 q20 ∷
   rw 19 q16 ∷
   rw 20 q20 ∷
   rw 21 q16 ∷
   rw 22 q21 ∷
   rw 23 q21 ∷
   rw 24 q21 ∷
   rw 25 q20 ∷
   rw 26 q16 ∷
   rw 27 q21 ∷
   rw 28 q21 ∷
   rw 29 q21 ∷
   rw 30 q21 ∷
   rw 31 q21 ∷
   rw 32 q21 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q18 ∷
   rw 34 q20 ∷
   rw 35 q18 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q26 ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q18 ∷
   rw 36 q20 ∷
   rw 37 q18 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q26 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q18 ∷
   rw 38 q21 ∷
   rw 39 q18 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q18 ∷
   rw 39 q21 ∷
   rw 40 q18 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q18 ∷
   rw 40 q21 ∷
   rw 41 q18 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏乇乏") ∷
   rw 40 q18 ∷
   rw 41 q20 ∷
   rw 42 q18 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q26 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q18 ∷
   rw 43 q21 ∷
   rw 44 q18 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q18 ∷
   rw 44 q21 ∷
   rw 45 q18 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q18 ∷
   rw 45 q21 ∷
   rw 46 q18 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q18 ∷
   rw 46 q21 ∷
   rw 47 q18 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q18 ∷
   rw 47 q21 ∷
   rw 48 q18 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q18 ∷
   rw 48 q21 ∷
   rw 49 q18 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q22 ∷
   re 18 1 (ℓ "丼临丼") ∷
   rw 17 q23 ∷
   rw⁻ 18 q11 ∷
   rw 19 q24 ∷
   re 17 3 (ℓ "乄") ∷
   rw 18 q25 ∷
   re 20 1 (ℓ "丼临丼") ∷
   rw 19 q23 ∷
   rw⁻ 20 q11 ∷
   rw 21 q24 ∷
   re 19 3 (ℓ "乄") ∷
   rw 20 q25 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q23 ∷
   rw⁻ 22 q6 ∷
   rw 23 q24 ∷
   re 21 3 (ℓ "丧") ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q23 ∷
   rw⁻ 23 q6 ∷
   rw 24 q24 ∷
   re 22 3 (ℓ "丧") ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q23 ∷
   rw⁻ 24 q6 ∷
   rw 25 q24 ∷
   re 23 3 (ℓ "丧") ∷
   re 25 1 (ℓ "丼临丼") ∷
   rw 24 q23 ∷
   rw⁻ 25 q11 ∷
   rw 26 q24 ∷
   re 24 3 (ℓ "乄") ∷
   rw 25 q25 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q23 ∷
   rw⁻ 27 q6 ∷
   rw 28 q24 ∷
   re 26 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q23 ∷
   rw⁻ 28 q6 ∷
   rw 29 q24 ∷
   re 27 3 (ℓ "丧") ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q23 ∷
   rw⁻ 29 q6 ∷
   rw 30 q24 ∷
   re 28 3 (ℓ "丧") ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q23 ∷
   rw⁻ 30 q6 ∷
   rw 31 q24 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q23 ∷
   rw⁻ 31 q6 ∷
   rw 32 q24 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q23 ∷
   rw⁻ 32 q6 ∷
   rw 33 q24 ∷
   re 31 3 (ℓ "丧") ∷
   rw 11 q28 ∷
   rw 56 q4 ∷
   rw 55 q1 ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw 56 q2 ∷
   rw 55 q10 ∷
   rw⁻ 54 q1 ∷ []) Eq.refl
