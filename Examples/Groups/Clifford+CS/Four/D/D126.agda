{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D126 (W : Ws) where

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
  q3 = wE 629 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 113 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = wE 114 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q19 : Eqn
  q19 = wE 673 W
  q20 : Eqn
  q20 = wE 488 W
  q21 : Eqn
  q21 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q23 : Eqn
  q23 = wE 680 W
  q24 : Eqn
  q24 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q25 : Eqn
  q25 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q26 : Eqn
  q26 = wE 464 W
  q27 : Eqn
  q27 = wE 681 W
  q28 : Eqn
  q28 = wE 151 W

-- Bar(SSKSKK;2,3->0) passes groups of WBar(SSSKSS;~2,1->0) part3: 457 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part3 : ⟪ (ℓ "丘丧丧丧乄丧丧丘丘乆丘丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中丘乆中並丘並中中中乌中中乑中乑乑丠丠丠临丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘丧丧丧乄丧丧丘丘乆丘丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丘乆丘丠丠丠临丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part3 = derive (ℓ "丘丧丧丧乄丧丧丘丘乆丘丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中丘乆中並丘並中中中乌中中乑中乑乑丠丠丠临丠丠") (ℓ "丘丧丧丧乄丧丧丘丘乆丘丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丘乆丘丠丠丠临丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q1 ∷
   rw 49 q2 ∷
   rw⁻ 48 q1 ∷
   re 49 3 (ℓ "丽") ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q1 ∷
   rw 50 q5 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q6 ∷
   rw 47 q7 ∷
   rw⁻ 46 q4 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q1 ∷
   rw 46 q2 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q1 ∷
   rw 47 q5 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q6 ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q8 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q9 ∷
   rw 48 q10 ∷
   rw 47 q11 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q12 ∷
   re 47 5 (ℓ "中") ∷
   rw 49 q7 ∷
   rw⁻ 48 q4 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q1 ∷
   rw 48 q2 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q3 ∷
   rw 47 q4 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q1 ∷
   rw 49 q5 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q6 ∷
   rw 46 q7 ∷
   rw⁻ 45 q4 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q1 ∷
   rw 45 q2 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q1 ∷
   rw 46 q5 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q6 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q8 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q9 ∷
   rw 47 q10 ∷
   rw 46 q11 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q12 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q7 ∷
   rw⁻ 47 q4 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q1 ∷
   rw 47 q2 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q3 ∷
   rw 46 q4 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q1 ∷
   rw 48 q5 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q6 ∷
   rw⁻ 43 q13 ∷
   rw⁻ 44 q14 ∷
   rw⁻ 45 q13 ∷
   rw 44 q7 ∷
   rw⁻ 43 q4 ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw⁻ 44 q1 ∷
   rw 43 q15 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (ℓ "乔") ∷
   rw 43 q16 ∷
   rw 42 q4 ∷
   re 44 1 (ℓ "乏乇乏") ∷
   rw 43 q1 ∷
   rw 44 q17 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乑") ∷
   rw 44 q6 ∷
   re 43 1 (ℓ "乏丼临丼乏") ∷
   rw 49 q8 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q9 ∷
   rw 45 q18 ∷
   rw 44 q11 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q12 ∷
   re 44 5 (ℓ "乑") ∷
   rw 46 q7 ∷
   rw⁻ 45 q4 ∷
   re 44 1 (ℓ "乏乄乏") ∷
   rw⁻ 46 q1 ∷
   rw 45 q15 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (ℓ "乔") ∷
   rw 45 q16 ∷
   rw 44 q4 ∷
   re 46 1 (ℓ "乏乇乏") ∷
   rw 45 q1 ∷
   rw 46 q17 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乑") ∷
   rw 46 q6 ∷
   rw 43 q7 ∷
   rw⁻ 42 q4 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q1 ∷
   rw 42 q2 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q3 ∷
   rw 41 q4 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q1 ∷
   rw 43 q5 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q6 ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q8 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q9 ∷
   rw 44 q10 ∷
   rw 43 q11 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q12 ∷
   re 43 5 (ℓ "中") ∷
   rw 45 q7 ∷
   rw⁻ 44 q4 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q1 ∷
   rw 45 q5 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q6 ∷
   rw 42 q7 ∷
   rw⁻ 41 q4 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q1 ∷
   rw 42 q5 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q6 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q8 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q9 ∷
   rw 43 q10 ∷
   rw 42 q11 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q12 ∷
   re 42 5 (ℓ "中") ∷
   rw 44 q7 ∷
   rw⁻ 43 q4 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q1 ∷
   rw 43 q2 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q3 ∷
   rw 42 q4 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q1 ∷
   rw 44 q5 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q6 ∷
   rw 41 q7 ∷
   rw⁻ 40 q4 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q3 ∷
   rw 39 q4 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q1 ∷
   rw 41 q5 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q6 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q8 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q9 ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q12 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q7 ∷
   rw⁻ 42 q4 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q1 ∷
   rw 42 q2 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q3 ∷
   rw 41 q4 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q1 ∷
   rw 43 q5 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q6 ∷
   rw⁻ 38 q13 ∷
   rw⁻ 39 q14 ∷
   rw⁻ 40 q13 ∷
   rw 39 q7 ∷
   rw⁻ 38 q4 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q1 ∷
   rw 38 q15 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (ℓ "乔") ∷
   rw 38 q16 ∷
   rw 37 q4 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q1 ∷
   rw 39 q17 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q6 ∷
   re 38 1 (ℓ "乏丼临丼乏") ∷
   rw 44 q8 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q9 ∷
   rw 40 q18 ∷
   rw 39 q11 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q12 ∷
   re 39 5 (ℓ "乑") ∷
   rw 41 q7 ∷
   rw⁻ 40 q4 ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw⁻ 41 q1 ∷
   rw 40 q15 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (ℓ "乔") ∷
   rw 40 q16 ∷
   rw 39 q4 ∷
   re 41 1 (ℓ "乏乇乏") ∷
   rw 40 q1 ∷
   rw 41 q17 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q6 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 37 q14 ∷
   rw⁻ 38 q13 ∷
   rw 37 q7 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q1 ∷
   rw 36 q15 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (ℓ "乔") ∷
   rw 36 q16 ∷
   rw 35 q4 ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q1 ∷
   rw 37 q17 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q6 ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q8 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q9 ∷
   rw 38 q18 ∷
   rw 37 q11 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q12 ∷
   re 37 5 (ℓ "乑") ∷
   rw 39 q7 ∷
   rw⁻ 38 q4 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q1 ∷
   rw 38 q15 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (ℓ "乔") ∷
   rw 38 q16 ∷
   rw 37 q4 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q1 ∷
   rw 39 q17 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q6 ∷
   rw 34 q19 ∷
   rw 28 q20 ∷
   rw 66 q8 ∷
   rw 65 q21 ∷
   rw 64 q21 ∷
   rw 63 q22 ∷
   rw 62 q21 ∷
   rw 61 q21 ∷
   rw 60 q21 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 61 q12 ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw 60 q12 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q12 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q12 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q12 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q12 ∷
   rw 55 q23 ∷
   rw⁻ 54 q21 ∷
   rw⁻ 55 q21 ∷
   rw⁻ 56 q21 ∷
   rw⁻ 57 q22 ∷
   rw⁻ 58 q21 ∷
   rw⁻ 59 q21 ∷
   rw 62 q8 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q8 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q8 ∷
   re 62 3 (ℓ "乑") ∷
   rw 65 q8 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q8 ∷
   re 64 3 (ℓ "乑") ∷
   rw 67 q8 ∷
   re 65 3 (ℓ "乑") ∷
   rw 66 q12 ∷
   rw⁻ 53 q24 ∷
   rw⁻ 54 q24 ∷
   rw⁻ 55 q24 ∷
   rw⁻ 56 q25 ∷
   rw⁻ 57 q24 ∷
   rw⁻ 58 q24 ∷
   rw 59 q8 ∷
   rw 58 q21 ∷
   rw 57 q21 ∷
   rw 56 q22 ∷
   rw 55 q21 ∷
   rw 54 q21 ∷
   rw 53 q21 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q12 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q12 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q12 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q12 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q12 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q12 ∷
   rw 46 q26 ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw 47 q12 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q12 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q12 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q12 ∷
   rw 41 q26 ∷
   re 40 1 (ℓ "乏乄乏") ∷
   rw 42 q12 ∷
   rw 39 q26 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q12 ∷
   rw 39 q27 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 39 q21 ∷
   rw⁻ 40 q21 ∷
   rw⁻ 41 q22 ∷
   rw⁻ 42 q21 ∷
   rw⁻ 43 q21 ∷
   rw 46 q8 ∷
   re 44 3 (ℓ "乑") ∷
   rw 45 q28 ∷
   rw 48 q8 ∷
   re 46 3 (ℓ "乑") ∷
   rw 47 q28 ∷
   rw 50 q8 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q8 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q8 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q8 ∷
   re 51 3 (ℓ "乑") ∷
   rw 52 q28 ∷
   rw 55 q8 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q8 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q8 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q8 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q8 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q8 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q12 ∷
   rw⁻ 37 q24 ∷
   rw⁻ 38 q24 ∷
   rw⁻ 39 q24 ∷
   rw⁻ 40 q25 ∷
   rw⁻ 41 q24 ∷
   rw⁻ 42 q24 ∷
   rw 31 q23 ∷ []) Eq.refl
