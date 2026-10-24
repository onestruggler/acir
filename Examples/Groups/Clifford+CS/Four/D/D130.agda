{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D130 (W : Ws) where

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
  q1 = wE 31 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 629 W
  q7 : Eqn
  q7 = wE 27 W
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
  q21 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q23 : Eqn
  q23 = wE 507 W
  q24 : Eqn
  q24 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q25 : Eqn
  q25 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q26 : Eqn
  q26 = wE 464 W
  q27 : Eqn
  q27 = wE 508 W
  q28 : Eqn
  q28 = wE 151 W

-- Bar(SSKSKK;2,3->0) passes groups of WBar(SSKSKK;~2,1->0) part3: 445 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part3 : ⟪ (ℓ "丘丧丧乄丧乄乄丘丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中丘乆丘中並並中中中乌中中乑中乑乑丠丠临丠临临") ⟫ʷ ≈ ⟪ (ℓ "丘丧丧乄丧乄乄丘丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丘乆丘丠丠临丠临临丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part3 = derive (ℓ "丘丧丧乄丧乄乄丘丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丧丧乄丧乄乄乌乑业乑业中中中乑业中中丘乆丘中並並中中中乌中中乑中乑乑丠丠临丠临临") (ℓ "丘丧丧乄丧乄乄丘丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠丘乆丘丠丠临丠临临丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 48 q1 ∷
   rw 45 q2 ∷
   rw⁻ 44 q3 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q4 ∷
   rw 44 q5 ∷
   rw⁻ 43 q4 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q6 ∷
   rw 43 q3 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q4 ∷
   rw 45 q7 ∷
   rw 46 q4 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q1 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q8 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q9 ∷
   rw 46 q10 ∷
   rw 45 q11 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q12 ∷
   re 45 5 (ℓ "中") ∷
   rw 47 q2 ∷
   rw⁻ 46 q3 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q4 ∷
   rw 46 q5 ∷
   rw⁻ 45 q4 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q6 ∷
   rw 45 q3 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q4 ∷
   rw 47 q7 ∷
   rw 48 q4 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q4 ∷
   rw 43 q5 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q6 ∷
   rw 42 q3 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q4 ∷
   rw 44 q7 ∷
   rw 45 q4 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q1 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q8 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q9 ∷
   rw 45 q10 ∷
   rw 44 q11 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q12 ∷
   re 44 5 (ℓ "中") ∷
   rw 46 q2 ∷
   rw⁻ 45 q3 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q4 ∷
   rw 45 q5 ∷
   rw⁻ 44 q4 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q6 ∷
   rw 44 q3 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q4 ∷
   rw 46 q7 ∷
   rw 47 q4 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q1 ∷
   rw⁻ 41 q13 ∷
   rw⁻ 42 q14 ∷
   rw⁻ 43 q13 ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (ℓ "乏乄乏") ∷
   rw⁻ 42 q4 ∷
   rw 41 q15 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (ℓ "乔") ∷
   rw 41 q16 ∷
   rw 40 q3 ∷
   re 42 1 (ℓ "乏乇乏") ∷
   rw 41 q4 ∷
   rw 42 q17 ∷
   rw 43 q4 ∷
   re 41 3 (ℓ "乑") ∷
   rw 42 q1 ∷
   re 41 1 (ℓ "乏丼临丼乏") ∷
   rw 47 q8 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q9 ∷
   rw 43 q18 ∷
   rw 42 q11 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q12 ∷
   re 42 5 (ℓ "乑") ∷
   rw 44 q2 ∷
   rw⁻ 43 q3 ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw⁻ 44 q4 ∷
   rw 43 q15 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (ℓ "乔") ∷
   rw 43 q16 ∷
   rw 42 q3 ∷
   re 44 1 (ℓ "乏乇乏") ∷
   rw 43 q4 ∷
   rw 44 q17 ∷
   rw 45 q4 ∷
   re 43 3 (ℓ "乑") ∷
   rw 44 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q1 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q8 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q9 ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q12 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q2 ∷
   rw⁻ 42 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q4 ∷
   rw 42 q5 ∷
   rw⁻ 41 q4 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q6 ∷
   rw 41 q3 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q4 ∷
   rw 43 q7 ∷
   rw 44 q4 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q3 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q4 ∷
   rw 39 q5 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (ℓ "丽") ∷
   rw 39 q6 ∷
   rw 38 q3 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q4 ∷
   rw 40 q7 ∷
   rw 41 q4 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q8 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q9 ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q12 ∷
   re 40 5 (ℓ "中") ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q6 ∷
   rw 40 q3 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q4 ∷
   rw 42 q7 ∷
   rw 43 q4 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q4 ∷
   rw 38 q5 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (ℓ "丽") ∷
   rw 38 q6 ∷
   rw 37 q3 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q4 ∷
   rw 39 q7 ∷
   rw 40 q4 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q1 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q8 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q9 ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q12 ∷
   re 39 5 (ℓ "中") ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q1 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 37 q14 ∷
   rw⁻ 38 q13 ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q4 ∷
   rw 36 q15 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (ℓ "乔") ∷
   rw 36 q16 ∷
   rw 35 q3 ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q4 ∷
   rw 37 q17 ∷
   rw 38 q4 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q1 ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q8 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q9 ∷
   rw 38 q18 ∷
   rw 37 q11 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q12 ∷
   re 37 5 (ℓ "乑") ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q4 ∷
   rw 38 q15 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (ℓ "乔") ∷
   rw 38 q16 ∷
   rw 37 q3 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q4 ∷
   rw 39 q17 ∷
   rw 40 q4 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q1 ∷
   rw⁻ 34 q13 ∷
   rw⁻ 35 q14 ∷
   rw⁻ 36 q13 ∷
   rw 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q15 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "乔") ∷
   rw 34 q16 ∷
   rw 33 q3 ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q4 ∷
   rw 35 q17 ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q1 ∷
   re 34 1 (ℓ "乏丼临丼乏") ∷
   rw 40 q8 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q9 ∷
   rw 36 q18 ∷
   rw 35 q11 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q12 ∷
   re 35 5 (ℓ "乑") ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q4 ∷
   rw 36 q15 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (ℓ "乔") ∷
   rw 36 q16 ∷
   rw 35 q3 ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q4 ∷
   rw 37 q17 ∷
   rw 38 q4 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q1 ∷
   rw 32 q19 ∷
   rw 26 q20 ∷
   rw 64 q8 ∷
   rw 63 q21 ∷
   rw 62 q21 ∷
   rw 61 q22 ∷
   rw 60 q21 ∷
   rw 59 q22 ∷
   rw 58 q22 ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 59 q12 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q12 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q12 ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw 56 q12 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q12 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q12 ∷
   rw 53 q23 ∷
   rw⁻ 52 q22 ∷
   rw⁻ 53 q22 ∷
   rw⁻ 54 q21 ∷
   rw⁻ 55 q22 ∷
   rw⁻ 56 q21 ∷
   rw⁻ 57 q21 ∷
   rw 60 q8 ∷
   re 58 3 (ℓ "中") ∷
   rw 61 q8 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q8 ∷
   re 60 3 (ℓ "乑") ∷
   rw 63 q8 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q8 ∷
   re 62 3 (ℓ "乑") ∷
   rw 65 q8 ∷
   re 63 3 (ℓ "乑") ∷
   rw 64 q12 ∷
   rw⁻ 51 q24 ∷
   rw⁻ 52 q24 ∷
   rw⁻ 53 q25 ∷
   rw⁻ 54 q24 ∷
   rw⁻ 55 q25 ∷
   rw⁻ 56 q25 ∷
   rw 57 q8 ∷
   rw 56 q21 ∷
   rw 55 q21 ∷
   rw 54 q22 ∷
   rw 53 q21 ∷
   rw 52 q22 ∷
   rw 51 q22 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q12 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q12 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q12 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q12 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q12 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q12 ∷
   rw 44 q26 ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw 45 q12 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q12 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q12 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q12 ∷
   rw 39 q26 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q12 ∷
   rw 37 q26 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q12 ∷
   rw 37 q27 ∷
   rw⁻ 36 q22 ∷
   rw⁻ 37 q22 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 39 q22 ∷
   rw⁻ 40 q21 ∷
   rw⁻ 41 q21 ∷
   rw 44 q8 ∷
   re 42 3 (ℓ "乑") ∷
   rw 43 q28 ∷
   rw 46 q8 ∷
   re 44 3 (ℓ "乑") ∷
   rw 45 q28 ∷
   rw 48 q8 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q8 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q8 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q8 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q28 ∷
   rw 53 q8 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q8 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q8 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q8 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q8 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q8 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q12 ∷
   rw⁻ 35 q24 ∷
   rw⁻ 36 q24 ∷
   rw⁻ 37 q25 ∷
   rw⁻ 38 q24 ∷
   rw⁻ 39 q25 ∷
   rw⁻ 40 q25 ∷
   rw 29 q23 ∷ []) Eq.refl
