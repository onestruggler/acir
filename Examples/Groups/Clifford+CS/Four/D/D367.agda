{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D367 (W : Ws) where

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
  q1 = wE 7 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 629 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 113 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q10 : Eqn
  q10 = wE 114 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 5 W
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
  q20 = wE 557 W
  q21 : Eqn
  q21 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q23 : Eqn
  q23 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q24 : Eqn
  q24 = wE 566 W
  q25 : Eqn
  q25 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q26 : Eqn
  q26 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q27 : Eqn
  q27 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q28 : Eqn
  q28 = wE 464 W
  q29 : Eqn
  q29 = wE 567 W

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part4: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中乏丧並乏丘並乆丘中中中中中中中乌中中中乑中中临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘丧丧丧乄丧丧乌临与临与丠丠丠临与丠丠丠丠丠丠中中中中中乏丧乏乏乄且丧丧丧丧丧丧丧丧丧乏乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part4 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中乏丧並乏丘並乆丘中中中中中中中乌中中中乑中中临与临与丠丠丠临与丠丠丠丠丠丠") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘丧丧丧乄丧丧乌临与临与丠丠丠临与丠丠丠丠丠丠中中中中中乏丧乏乏乄且丧丧丧丧丧丧丧丧丧乏乌中中中乑中中")
  (rw 79 q1 ∷
   rw⁻ 78 q2 ∷
   re 79 3 (ℓ "丽") ∷
   rw 79 q3 ∷
   rw 78 q4 ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q2 ∷
   rw 80 q5 ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "中") ∷
   rw 80 q6 ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q7 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q8 ∷
   rw 81 q9 ∷
   rw 80 q10 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q11 ∷
   re 80 5 (ℓ "中") ∷
   rw 82 q12 ∷
   rw⁻ 81 q4 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q2 ∷
   rw 81 q1 ∷
   rw⁻ 80 q2 ∷
   re 81 3 (ℓ "丽") ∷
   rw 81 q3 ∷
   rw 80 q4 ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q2 ∷
   rw 82 q5 ∷
   rw 83 q2 ∷
   re 81 3 (ℓ "中") ∷
   rw 82 q6 ∷
   rw 79 q12 ∷
   rw⁻ 78 q4 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q2 ∷
   rw 78 q1 ∷
   rw⁻ 77 q2 ∷
   re 78 3 (ℓ "丽") ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q2 ∷
   rw 79 q5 ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "中") ∷
   rw 79 q6 ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q7 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q8 ∷
   rw 80 q9 ∷
   rw 79 q10 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q11 ∷
   re 79 5 (ℓ "中") ∷
   rw 81 q12 ∷
   rw⁻ 80 q4 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q2 ∷
   rw 80 q1 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (ℓ "丽") ∷
   rw 80 q3 ∷
   rw 79 q4 ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q2 ∷
   rw 81 q5 ∷
   rw 82 q2 ∷
   re 80 3 (ℓ "中") ∷
   rw 81 q6 ∷
   rw⁻ 76 q13 ∷
   rw⁻ 77 q14 ∷
   rw⁻ 78 q13 ∷
   rw 77 q12 ∷
   rw⁻ 76 q4 ∷
   re 75 1 (ℓ "乏乄乏") ∷
   rw⁻ 77 q2 ∷
   rw 76 q15 ∷
   rw⁻ 75 q2 ∷
   re 76 3 (ℓ "乔") ∷
   rw 76 q16 ∷
   rw 75 q4 ∷
   re 77 1 (ℓ "乏乇乏") ∷
   rw 76 q2 ∷
   rw 77 q17 ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "乑") ∷
   rw 77 q6 ∷
   re 76 1 (ℓ "乏丼临丼乏") ∷
   rw 82 q7 ∷
   re 80 3 (ℓ "乓") ∷
   rw 79 q8 ∷
   rw 78 q18 ∷
   rw 77 q10 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q11 ∷
   re 77 5 (ℓ "乑") ∷
   rw 79 q12 ∷
   rw⁻ 78 q4 ∷
   re 77 1 (ℓ "乏乄乏") ∷
   rw⁻ 79 q2 ∷
   rw 78 q15 ∷
   rw⁻ 77 q2 ∷
   re 78 3 (ℓ "乔") ∷
   rw 78 q16 ∷
   rw 77 q4 ∷
   re 79 1 (ℓ "乏乇乏") ∷
   rw 78 q2 ∷
   rw 79 q17 ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "乑") ∷
   rw 79 q6 ∷
   rw 76 q12 ∷
   rw⁻ 75 q4 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q2 ∷
   rw 75 q1 ∷
   rw⁻ 74 q2 ∷
   re 75 3 (ℓ "丽") ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q2 ∷
   rw 76 q5 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q6 ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q7 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q8 ∷
   rw 77 q9 ∷
   rw 76 q10 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q11 ∷
   re 76 5 (ℓ "中") ∷
   rw 78 q12 ∷
   rw⁻ 77 q4 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q2 ∷
   rw 77 q1 ∷
   rw⁻ 76 q2 ∷
   re 77 3 (ℓ "丽") ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q2 ∷
   rw 78 q5 ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q6 ∷
   rw 75 q12 ∷
   rw⁻ 74 q4 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q2 ∷
   rw 74 q1 ∷
   rw⁻ 73 q2 ∷
   re 74 3 (ℓ "丽") ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q2 ∷
   rw 75 q5 ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q6 ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q7 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q8 ∷
   rw 76 q9 ∷
   rw 75 q10 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q11 ∷
   re 75 5 (ℓ "中") ∷
   rw 77 q12 ∷
   rw⁻ 76 q4 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q2 ∷
   rw 76 q1 ∷
   rw⁻ 75 q2 ∷
   re 76 3 (ℓ "丽") ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q2 ∷
   rw 77 q5 ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q6 ∷
   rw 74 q12 ∷
   rw⁻ 73 q4 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q2 ∷
   rw 73 q1 ∷
   rw⁻ 72 q2 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q2 ∷
   rw 74 q5 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q6 ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q7 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q8 ∷
   rw 75 q9 ∷
   rw 74 q10 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q11 ∷
   re 74 5 (ℓ "中") ∷
   rw 76 q12 ∷
   rw⁻ 75 q4 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q2 ∷
   rw 75 q1 ∷
   rw⁻ 74 q2 ∷
   re 75 3 (ℓ "丽") ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q2 ∷
   rw 76 q5 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q6 ∷
   rw 73 q12 ∷
   rw⁻ 72 q4 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q2 ∷
   rw 72 q1 ∷
   rw⁻ 71 q2 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q2 ∷
   rw 73 q5 ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q6 ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q7 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q8 ∷
   rw 74 q9 ∷
   rw 73 q10 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q11 ∷
   re 73 5 (ℓ "中") ∷
   rw 75 q12 ∷
   rw⁻ 74 q4 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q2 ∷
   rw 74 q1 ∷
   rw⁻ 73 q2 ∷
   re 74 3 (ℓ "丽") ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q2 ∷
   rw 75 q5 ∷
   rw 76 q2 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q6 ∷
   rw 72 q12 ∷
   rw⁻ 71 q4 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw⁻ 72 q2 ∷
   rw 71 q1 ∷
   rw⁻ 70 q2 ∷
   re 71 3 (ℓ "丽") ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q2 ∷
   rw 72 q5 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q6 ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q7 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q8 ∷
   rw 73 q9 ∷
   rw 72 q10 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q11 ∷
   re 72 5 (ℓ "中") ∷
   rw 74 q12 ∷
   rw⁻ 73 q4 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q2 ∷
   rw 73 q1 ∷
   rw⁻ 72 q2 ∷
   re 73 3 (ℓ "丽") ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "乏丶乏") ∷
   rw 73 q2 ∷
   rw 74 q5 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "中") ∷
   rw 74 q6 ∷
   rw 71 q12 ∷
   rw⁻ 70 q4 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q2 ∷
   rw 70 q1 ∷
   rw⁻ 69 q2 ∷
   re 70 3 (ℓ "丽") ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q2 ∷
   rw 71 q5 ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q6 ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q7 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q8 ∷
   rw 72 q9 ∷
   rw 71 q10 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q11 ∷
   re 71 5 (ℓ "中") ∷
   rw 73 q12 ∷
   rw⁻ 72 q4 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q2 ∷
   rw 72 q1 ∷
   rw⁻ 71 q2 ∷
   re 72 3 (ℓ "丽") ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q2 ∷
   rw 73 q5 ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q6 ∷
   rw 68 q19 ∷
   rw 62 q20 ∷
   rw 111 q7 ∷
   rw 110 q21 ∷
   rw 109 q21 ∷
   rw 108 q21 ∷
   rw 107 q21 ∷
   rw 106 q21 ∷
   rw 105 q21 ∷
   rw 104 q22 ∷
   rw 103 q23 ∷
   rw 102 q21 ∷
   rw 101 q21 ∷
   rw 100 q21 ∷
   rw 99 q22 ∷
   rw 98 q23 ∷
   rw 97 q22 ∷
   rw 96 q23 ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q11 ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q11 ∷
   re 93 1 (ℓ "乏乄乏") ∷
   rw 95 q11 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q11 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q11 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 92 q11 ∷
   rw 91 q24 ∷
   rw⁻ 90 q23 ∷
   rw⁻ 91 q22 ∷
   rw⁻ 92 q23 ∷
   rw⁻ 93 q22 ∷
   rw⁻ 94 q21 ∷
   rw⁻ 95 q21 ∷
   rw⁻ 96 q21 ∷
   rw⁻ 97 q23 ∷
   rw⁻ 98 q22 ∷
   rw⁻ 99 q21 ∷
   rw⁻ 100 q21 ∷
   rw⁻ 101 q21 ∷
   rw⁻ 102 q21 ∷
   rw⁻ 103 q21 ∷
   rw⁻ 104 q21 ∷
   rw 107 q7 ∷
   re 105 3 (ℓ "中") ∷
   rw 108 q7 ∷
   re 106 3 (ℓ "中") ∷
   rw 109 q7 ∷
   re 107 3 (ℓ "中") ∷
   rw 110 q7 ∷
   re 108 3 (ℓ "乑") ∷
   rw 111 q7 ∷
   re 109 3 (ℓ "中") ∷
   rw 112 q7 ∷
   re 110 3 (ℓ "中") ∷
   rw 111 q11 ∷
   rw⁻ 89 q25 ∷
   rw⁻ 90 q26 ∷
   rw⁻ 91 q25 ∷
   rw⁻ 92 q26 ∷
   rw⁻ 93 q27 ∷
   rw⁻ 94 q27 ∷
   rw⁻ 95 q27 ∷
   rw⁻ 96 q25 ∷
   rw⁻ 97 q26 ∷
   rw⁻ 98 q27 ∷
   rw⁻ 99 q27 ∷
   rw⁻ 100 q27 ∷
   rw⁻ 101 q27 ∷
   rw⁻ 102 q27 ∷
   rw⁻ 103 q27 ∷
   rw 104 q7 ∷
   rw 103 q21 ∷
   rw 102 q21 ∷
   rw 101 q21 ∷
   rw 100 q21 ∷
   rw 99 q21 ∷
   rw 98 q21 ∷
   rw 97 q22 ∷
   rw 96 q23 ∷
   rw 95 q21 ∷
   rw 94 q21 ∷
   rw 93 q21 ∷
   rw 92 q22 ∷
   rw 91 q23 ∷
   rw 90 q22 ∷
   rw 89 q23 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q11 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q11 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q11 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q11 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q11 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q11 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q11 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q11 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q11 ∷
   rw 79 q28 ∷
   re 78 1 (ℓ "乏乄乏") ∷
   rw 80 q11 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q11 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q11 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q11 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q11 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q11 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q11 ∷
   rw 73 q29 ∷
   rw⁻ 72 q23 ∷
   rw⁻ 73 q22 ∷
   rw⁻ 74 q23 ∷
   rw⁻ 75 q22 ∷
   rw⁻ 76 q21 ∷
   rw⁻ 77 q21 ∷
   rw⁻ 78 q21 ∷
   rw⁻ 79 q23 ∷
   rw⁻ 80 q22 ∷
   rw⁻ 81 q21 ∷
   rw⁻ 82 q21 ∷
   rw⁻ 83 q21 ∷
   rw⁻ 84 q21 ∷
   rw⁻ 85 q21 ∷
   rw⁻ 86 q21 ∷
   rw 89 q7 ∷
   re 87 3 (ℓ "中") ∷
   rw 90 q7 ∷
   re 88 3 (ℓ "中") ∷
   rw 91 q7 ∷
   re 89 3 (ℓ "中") ∷
   rw 92 q7 ∷
   re 90 3 (ℓ "中") ∷
   rw 93 q7 ∷
   re 91 3 (ℓ "中") ∷
   rw 94 q7 ∷ []) Eq.refl
