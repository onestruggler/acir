{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D233 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = wE 140 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 823 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 629 W
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 113 W
  q15 : Eqn
  q15 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q16 : Eqn
  q16 = wE 114 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = wE 630 W
  q19 : Eqn
  q19 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q20 : Eqn
  q20 = wE 673 W

-- Bar(SSSKSS;2,3->0) passes groups of WBar(SSKSKK;~2,1->0) part0: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part0 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丧丧乄丧乄乄丘丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丘乆丘丠丠临丠临临") ⟫ʷ ≈ ⟪ (ℓ "丘丧丧乄丧乄乄丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中並丘丽並乆丘乌中中中乑中中临与临与丠丠丠临与丠丠丠丠丠丠丘乆丘丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part0 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丧丧乄丧乄乄丘丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丘乆丘丠丠临丠临临") (ℓ "丘丧丧乄丧乄乄丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中並丘丽並乆丘乌中中中乑中中临与临与丠丠丠临与丠丠丠丠丠丠丘乆丘丠丠临丠临临")
  (rw 39 q1 ∷
   rw⁻ 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q4 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q5 ∷
   rw 31 q4 ∷
   rw⁻ 30 q5 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q5 ∷
   rw 30 q4 ∷
   rw⁻ 29 q5 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q5 ∷
   rw 29 q3 ∷
   rw⁻ 28 q5 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q5 ∷
   rw 28 q4 ∷
   rw⁻ 27 q5 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q5 ∷
   rw 27 q4 ∷
   rw⁻ 26 q5 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q5 ∷
   rw 26 q4 ∷
   rw⁻ 25 q5 ∷
   re 26 3 (ℓ "丽") ∷
   rw⁻ 24 q6 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q5 ∷
   rw 24 q4 ∷
   rw⁻ 23 q5 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q5 ∷
   rw 23 q4 ∷
   rw⁻ 22 q5 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q5 ∷
   rw 22 q4 ∷
   rw⁻ 21 q5 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q5 ∷
   rw 21 q4 ∷
   rw⁻ 20 q5 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q5 ∷
   rw 20 q4 ∷
   rw⁻ 19 q5 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q5 ∷
   rw 19 q4 ∷
   rw⁻ 18 q5 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q5 ∷
   rw 18 q4 ∷
   rw⁻ 17 q5 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q5 ∷
   rw 17 q4 ∷
   rw⁻ 16 q5 ∷
   re 17 3 (ℓ "丽") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q5 ∷
   rw 16 q4 ∷
   rw⁻ 15 q5 ∷
   re 16 3 (ℓ "丽") ∷
   rw⁻ 14 q7 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q5 ∷
   rw 14 q3 ∷
   rw⁻ 13 q5 ∷
   re 14 3 (ℓ "乔") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q5 ∷
   rw 13 q4 ∷
   rw⁻ 12 q5 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q5 ∷
   rw 12 q4 ∷
   rw⁻ 11 q5 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q5 ∷
   rw 11 q4 ∷
   rw⁻ 10 q5 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q5 ∷
   rw 10 q4 ∷
   rw⁻ 9 q5 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q5 ∷
   rw 9 q4 ∷
   rw⁻ 8 q5 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q5 ∷
   rw 8 q4 ∷
   rw⁻ 7 q5 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 6 q6 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q10 ∷
   rw 7 q2 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 10 q9 ∷
   rw 11 q10 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q6 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q5 ∷
   rw 16 q9 ∷
   rw 17 q5 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q5 ∷
   rw 17 q9 ∷
   rw 18 q5 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q5 ∷
   rw 18 q9 ∷
   rw 19 q5 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q5 ∷
   rw 19 q9 ∷
   rw 20 q5 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q5 ∷
   rw 20 q9 ∷
   rw 21 q5 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q5 ∷
   rw 21 q9 ∷
   rw 22 q5 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q5 ∷
   rw 22 q10 ∷
   rw 23 q5 ∷
   re 21 3 (ℓ "乑") ∷
   rw 22 q7 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q5 ∷
   rw 24 q9 ∷
   rw 25 q5 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q5 ∷
   rw 25 q9 ∷
   rw 26 q5 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q5 ∷
   rw 26 q9 ∷
   rw 27 q5 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q5 ∷
   rw 27 q9 ∷
   rw 28 q5 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q5 ∷
   rw 28 q9 ∷
   rw 29 q5 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q5 ∷
   rw 29 q9 ∷
   rw 30 q5 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q5 ∷
   rw 30 q9 ∷
   rw 31 q5 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q5 ∷
   rw 31 q9 ∷
   rw 32 q5 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q5 ∷
   rw 32 q9 ∷
   rw 33 q5 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q6 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q5 ∷
   rw 34 q9 ∷
   rw 35 q5 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q5 ∷
   rw 35 q9 ∷
   rw 36 q5 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   rw 36 q9 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q5 ∷
   rw 37 q10 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "乑") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q5 ∷
   rw 38 q9 ∷
   rw 39 q5 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q5 ∷
   rw 39 q9 ∷
   rw 40 q5 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q11 ∷
   rw 40 q1 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q5 ∷
   rw 39 q4 ∷
   rw⁻ 38 q5 ∷
   re 39 3 (ℓ "丽") ∷
   rw 39 q12 ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q5 ∷
   rw 40 q9 ∷
   rw 41 q5 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q11 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q13 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q14 ∷
   rw 41 q15 ∷
   rw 40 q16 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q17 ∷
   re 40 5 (ℓ "中") ∷
   rw 42 q1 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q5 ∷
   rw 41 q4 ∷
   rw⁻ 40 q5 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q12 ∷
   rw 40 q2 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q5 ∷
   rw 42 q9 ∷
   rw 43 q5 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q11 ∷
   rw 39 q1 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q5 ∷
   rw 38 q4 ∷
   rw⁻ 37 q5 ∷
   re 38 3 (ℓ "丽") ∷
   rw 38 q12 ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q5 ∷
   rw 39 q9 ∷
   rw 40 q5 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q11 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q13 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q14 ∷
   rw 40 q15 ∷
   rw 39 q16 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q17 ∷
   re 39 5 (ℓ "中") ∷
   rw 41 q1 ∷
   rw⁻ 40 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q5 ∷
   rw 40 q4 ∷
   rw⁻ 39 q5 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q12 ∷
   rw 39 q2 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q5 ∷
   rw 41 q9 ∷
   rw 42 q5 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q11 ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw⁻ 38 q5 ∷
   rw 37 q3 ∷
   rw⁻ 36 q5 ∷
   re 37 3 (ℓ "乔") ∷
   rw 37 q18 ∷
   rw 36 q2 ∷
   re 38 1 (ℓ "乏乇乏") ∷
   rw 37 q5 ∷
   rw 38 q10 ∷
   rw 39 q5 ∷
   re 37 3 (ℓ "乑") ∷
   rw 38 q11 ∷
   re 37 1 (ℓ "乏丼临丼乏") ∷
   rw 43 q13 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q14 ∷
   rw 39 q19 ∷
   rw 38 q16 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q17 ∷
   re 38 5 (ℓ "乑") ∷
   rw 40 q1 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw⁻ 40 q5 ∷
   rw 39 q3 ∷
   rw⁻ 38 q5 ∷
   re 39 3 (ℓ "乔") ∷
   rw 39 q18 ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏乇乏") ∷
   rw 39 q5 ∷
   rw 40 q10 ∷
   rw 41 q5 ∷
   re 39 3 (ℓ "乑") ∷
   rw 40 q11 ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q5 ∷
   rw 36 q4 ∷
   rw⁻ 35 q5 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q12 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q5 ∷
   rw 37 q9 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q11 ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q13 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q14 ∷
   rw 38 q15 ∷
   rw 37 q16 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q17 ∷
   re 37 5 (ℓ "中") ∷
   rw 39 q1 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q5 ∷
   rw 38 q4 ∷
   rw⁻ 37 q5 ∷
   re 38 3 (ℓ "丽") ∷
   rw 38 q12 ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q5 ∷
   rw 39 q9 ∷
   rw 40 q5 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q11 ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q5 ∷
   rw 35 q4 ∷
   rw⁻ 34 q5 ∷
   re 35 3 (ℓ "丽") ∷
   rw 35 q12 ∷
   rw 34 q2 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   rw 36 q9 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q11 ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q13 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q14 ∷
   rw 37 q15 ∷
   rw 36 q16 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q17 ∷
   re 36 5 (ℓ "中") ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q5 ∷
   rw 37 q4 ∷
   rw⁻ 36 q5 ∷
   re 37 3 (ℓ "丽") ∷
   rw 37 q12 ∷
   rw 36 q2 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q5 ∷
   rw 38 q9 ∷
   rw 39 q5 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q11 ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q5 ∷
   rw 34 q4 ∷
   rw⁻ 33 q5 ∷
   re 34 3 (ℓ "丽") ∷
   rw 34 q12 ∷
   rw 33 q2 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q5 ∷
   rw 35 q9 ∷
   rw 36 q5 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q11 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q13 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q14 ∷
   rw 36 q15 ∷
   rw 35 q16 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q17 ∷
   re 35 5 (ℓ "中") ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q5 ∷
   rw 36 q4 ∷
   rw⁻ 35 q5 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q12 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q5 ∷
   rw 37 q9 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q11 ∷
   rw 32 q20 ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q5 ∷
   rw 32 q4 ∷
   rw⁻ 31 q5 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q12 ∷ []) Eq.refl
