{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D365 (W : Ws) where

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
  q1 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q2 : Eqn
  q2 = wE 114 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 629 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 113 W
  q13 : Eqn
  q13 = wE 673 W
  q14 : Eqn
  q14 = wE 557 W
  q15 : Eqn
  q15 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = wE 986 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q20 : Eqn
  q20 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q21 : Eqn
  q21 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q22 : Eqn
  q22 = wE 464 W
  q23 : Eqn
  q23 = wE 987 W
  q24 : Eqn
  q24 = wE 151 W

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part2: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中丘乏丼丠乖丼乏丘中中乑业中中中中中中中中中乌中中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中丘乏丧並乏並乆丘临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part2 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中丘乏丼丠乖丼乏丘中中乑业中中中中中中中中中乌中中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中丘乏丧並乏並乆丘临与临与丠丠丠临与丠丠丠丠丠丠")
  (rw 30 q1 ∷
   rw 29 q2 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q3 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q4 ∷
   rw⁻ 30 q5 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q6 ∷
   rw 30 q7 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q8 ∷
   rw 29 q5 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q6 ∷
   rw 31 q9 ∷
   rw 32 q6 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q10 ∷
   rw 28 q4 ∷
   rw⁻ 27 q5 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q6 ∷
   rw 27 q7 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q8 ∷
   rw 26 q5 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q10 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q11 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q12 ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q3 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q4 ∷
   rw⁻ 29 q5 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q6 ∷
   rw 29 q7 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q8 ∷
   rw 28 q5 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q6 ∷
   rw 30 q9 ∷
   rw 31 q6 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q10 ∷
   rw 27 q4 ∷
   rw⁻ 26 q5 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q6 ∷
   rw 26 q7 ∷
   rw⁻ 25 q6 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q8 ∷
   rw 25 q5 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q6 ∷
   rw 27 q9 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q10 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q11 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q12 ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q3 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q4 ∷
   rw⁻ 28 q5 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q6 ∷
   rw 28 q7 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q8 ∷
   rw 27 q5 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q6 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q10 ∷
   rw 26 q4 ∷
   rw⁻ 25 q5 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q6 ∷
   rw 25 q7 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q8 ∷
   rw 24 q5 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q6 ∷
   rw 26 q9 ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q10 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q11 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q12 ∷
   rw 27 q1 ∷
   rw 26 q2 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q3 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q4 ∷
   rw⁻ 27 q5 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q6 ∷
   rw 27 q7 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q8 ∷
   rw 26 q5 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q10 ∷
   rw 23 q13 ∷
   rw 17 q14 ∷
   rw 93 q11 ∷
   rw 92 q15 ∷
   rw 91 q16 ∷
   rw 90 q15 ∷
   rw 89 q15 ∷
   rw 88 q15 ∷
   rw 87 q15 ∷
   rw 86 q16 ∷
   rw 85 q15 ∷
   rw 84 q15 ∷
   rw 83 q15 ∷
   rw 82 q17 ∷
   rw 81 q17 ∷
   rw 80 q17 ∷
   rw 79 q17 ∷
   rw 78 q17 ∷
   rw 77 q17 ∷
   rw 76 q17 ∷
   rw 75 q17 ∷
   rw 74 q17 ∷
   rw 73 q15 ∷
   rw 72 q16 ∷
   rw 71 q15 ∷
   rw 70 q15 ∷
   rw 69 q15 ∷
   rw 68 q17 ∷
   rw 67 q17 ∷
   rw 66 q17 ∷
   rw 65 q17 ∷
   rw 64 q17 ∷
   rw 63 q17 ∷
   rw 62 q17 ∷
   rw 61 q17 ∷
   rw 60 q17 ∷
   rw 59 q17 ∷
   rw 58 q17 ∷
   rw 57 q17 ∷
   rw 56 q17 ∷
   rw 55 q17 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw 52 q17 ∷
   rw 51 q17 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q3 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q3 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw 50 q3 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q3 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q3 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q3 ∷
   rw 46 q18 ∷
   rw⁻ 45 q17 ∷
   rw⁻ 46 q17 ∷
   rw⁻ 47 q17 ∷
   rw⁻ 48 q17 ∷
   rw⁻ 49 q17 ∷
   rw⁻ 50 q17 ∷
   rw⁻ 51 q17 ∷
   rw⁻ 52 q17 ∷
   rw⁻ 53 q17 ∷
   rw⁻ 54 q17 ∷
   rw⁻ 55 q17 ∷
   rw⁻ 56 q17 ∷
   rw⁻ 57 q17 ∷
   rw⁻ 58 q17 ∷
   rw⁻ 59 q17 ∷
   rw⁻ 60 q17 ∷
   rw⁻ 61 q17 ∷
   rw⁻ 62 q17 ∷
   rw⁻ 63 q15 ∷
   rw⁻ 64 q15 ∷
   rw⁻ 65 q15 ∷
   rw⁻ 66 q16 ∷
   rw⁻ 67 q15 ∷
   rw⁻ 68 q17 ∷
   rw⁻ 69 q17 ∷
   rw⁻ 70 q17 ∷
   rw⁻ 71 q17 ∷
   rw⁻ 72 q17 ∷
   rw⁻ 73 q17 ∷
   rw⁻ 74 q17 ∷
   rw⁻ 75 q17 ∷
   rw⁻ 76 q17 ∷
   rw⁻ 77 q15 ∷
   rw⁻ 78 q15 ∷
   rw⁻ 79 q15 ∷
   rw⁻ 80 q16 ∷
   rw⁻ 81 q15 ∷
   rw⁻ 82 q15 ∷
   rw⁻ 83 q15 ∷
   rw⁻ 84 q15 ∷
   rw⁻ 85 q16 ∷
   rw⁻ 86 q15 ∷
   rw 89 q11 ∷
   re 87 3 (ℓ "中") ∷
   rw 90 q11 ∷
   re 88 3 (ℓ "中") ∷
   rw 91 q11 ∷
   re 89 3 (ℓ "中") ∷
   rw 92 q11 ∷
   re 90 3 (ℓ "乑") ∷
   rw 93 q11 ∷
   re 91 3 (ℓ "中") ∷
   rw 94 q11 ∷
   re 92 3 (ℓ "中") ∷
   rw 93 q3 ∷
   rw⁻ 44 q19 ∷
   rw⁻ 45 q19 ∷
   rw⁻ 46 q19 ∷
   rw⁻ 47 q19 ∷
   rw⁻ 48 q19 ∷
   rw⁻ 49 q19 ∷
   rw⁻ 50 q19 ∷
   rw⁻ 51 q19 ∷
   rw⁻ 52 q19 ∷
   rw⁻ 53 q19 ∷
   rw⁻ 54 q19 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q19 ∷
   rw⁻ 57 q19 ∷
   rw⁻ 58 q19 ∷
   rw⁻ 59 q19 ∷
   rw⁻ 60 q19 ∷
   rw⁻ 61 q19 ∷
   rw⁻ 62 q20 ∷
   rw⁻ 63 q20 ∷
   rw⁻ 64 q20 ∷
   rw⁻ 65 q21 ∷
   rw⁻ 66 q20 ∷
   rw⁻ 67 q19 ∷
   rw⁻ 68 q19 ∷
   rw⁻ 69 q19 ∷
   rw⁻ 70 q19 ∷
   rw⁻ 71 q19 ∷
   rw⁻ 72 q19 ∷
   rw⁻ 73 q19 ∷
   rw⁻ 74 q19 ∷
   rw⁻ 75 q19 ∷
   rw⁻ 76 q20 ∷
   rw⁻ 77 q20 ∷
   rw⁻ 78 q20 ∷
   rw⁻ 79 q21 ∷
   rw⁻ 80 q20 ∷
   rw⁻ 81 q20 ∷
   rw⁻ 82 q20 ∷
   rw⁻ 83 q20 ∷
   rw⁻ 84 q21 ∷
   rw⁻ 85 q20 ∷
   rw 86 q11 ∷
   rw 85 q15 ∷
   rw 84 q16 ∷
   rw 83 q15 ∷
   rw 82 q15 ∷
   rw 81 q15 ∷
   rw 80 q15 ∷
   rw 79 q16 ∷
   rw 78 q15 ∷
   rw 77 q15 ∷
   rw 76 q15 ∷
   rw 75 q17 ∷
   rw 74 q17 ∷
   rw 73 q17 ∷
   rw 72 q17 ∷
   rw 71 q17 ∷
   rw 70 q17 ∷
   rw 69 q17 ∷
   rw 68 q17 ∷
   rw 67 q17 ∷
   rw 66 q15 ∷
   rw 65 q16 ∷
   rw 64 q15 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 61 q17 ∷
   rw 60 q17 ∷
   rw 59 q17 ∷
   rw 58 q17 ∷
   rw 57 q17 ∷
   rw 56 q17 ∷
   rw 55 q17 ∷
   rw 54 q17 ∷
   rw 53 q17 ∷
   rw 52 q17 ∷
   rw 51 q17 ∷
   rw 50 q17 ∷
   rw 49 q17 ∷
   rw 48 q17 ∷
   rw 47 q17 ∷
   rw 46 q17 ∷
   rw 45 q17 ∷
   rw 44 q17 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q3 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q3 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q3 ∷
   rw 34 q22 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q3 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q3 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q3 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q3 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q3 ∷
   rw 28 q23 ∷
   rw⁻ 27 q17 ∷
   rw⁻ 28 q17 ∷
   rw⁻ 29 q17 ∷
   rw⁻ 30 q17 ∷
   rw⁻ 31 q17 ∷
   rw⁻ 32 q17 ∷
   rw⁻ 33 q17 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q17 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 38 q17 ∷
   rw⁻ 39 q17 ∷
   rw⁻ 40 q17 ∷
   rw⁻ 41 q17 ∷
   rw⁻ 42 q17 ∷
   rw⁻ 43 q17 ∷
   rw⁻ 44 q17 ∷
   rw⁻ 45 q15 ∷
   rw⁻ 46 q15 ∷
   rw⁻ 47 q15 ∷
   rw⁻ 48 q16 ∷
   rw⁻ 49 q15 ∷
   rw⁻ 50 q17 ∷
   rw⁻ 51 q17 ∷
   rw⁻ 52 q17 ∷
   rw⁻ 53 q17 ∷
   rw⁻ 54 q17 ∷
   rw⁻ 55 q17 ∷
   rw⁻ 56 q17 ∷
   rw⁻ 57 q17 ∷
   rw⁻ 58 q17 ∷
   rw⁻ 59 q15 ∷
   rw⁻ 60 q15 ∷
   rw⁻ 61 q15 ∷
   rw⁻ 62 q16 ∷
   rw⁻ 63 q15 ∷
   rw⁻ 64 q15 ∷
   rw⁻ 65 q15 ∷
   rw⁻ 66 q15 ∷
   rw⁻ 67 q16 ∷
   rw⁻ 68 q15 ∷
   rw 71 q11 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q11 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q11 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q11 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q11 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q11 ∷
   re 74 3 (ℓ "中") ∷
   rw 77 q11 ∷
   re 75 3 (ℓ "乑") ∷
   rw 76 q24 ∷
   rw 79 q11 ∷
   re 77 3 (ℓ "中") ∷
   rw 80 q11 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q11 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q11 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q11 ∷
   re 81 3 (ℓ "中") ∷
   rw 84 q11 ∷
   re 82 3 (ℓ "中") ∷
   rw 85 q11 ∷
   re 83 3 (ℓ "中") ∷
   rw 86 q11 ∷
   re 84 3 (ℓ "中") ∷
   rw 87 q11 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q3 ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q19 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q19 ∷
   rw⁻ 31 q19 ∷
   rw⁻ 32 q19 ∷
   rw⁻ 33 q19 ∷
   rw⁻ 34 q19 ∷
   rw⁻ 35 q19 ∷
   rw⁻ 36 q19 ∷
   rw⁻ 37 q19 ∷
   rw⁻ 38 q19 ∷
   rw⁻ 39 q19 ∷
   rw⁻ 40 q19 ∷
   rw⁻ 41 q19 ∷
   rw⁻ 42 q19 ∷
   rw⁻ 43 q19 ∷
   rw⁻ 44 q20 ∷
   rw⁻ 45 q20 ∷
   rw⁻ 46 q20 ∷
   rw⁻ 47 q21 ∷
   rw⁻ 48 q20 ∷
   rw⁻ 49 q19 ∷
   rw⁻ 50 q19 ∷
   rw⁻ 51 q19 ∷
   rw⁻ 52 q19 ∷
   rw⁻ 53 q19 ∷
   rw⁻ 54 q19 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q19 ∷
   rw⁻ 57 q19 ∷
   rw⁻ 58 q20 ∷
   rw⁻ 59 q20 ∷
   rw⁻ 60 q20 ∷
   rw⁻ 61 q21 ∷
   rw⁻ 62 q20 ∷
   rw⁻ 63 q20 ∷
   rw⁻ 64 q20 ∷
   rw⁻ 65 q20 ∷
   rw⁻ 66 q21 ∷
   rw⁻ 67 q20 ∷
   rw 20 q18 ∷
   rw 94 q4 ∷
   rw⁻ 93 q5 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw⁻ 94 q6 ∷
   rw 93 q7 ∷
   rw⁻ 92 q6 ∷
   re 93 3 (ℓ "丽") ∷
   rw 93 q8 ∷
   rw 92 q5 ∷
   re 94 1 (ℓ "乏丶乏") ∷
   rw 93 q6 ∷
   rw 94 q9 ∷ []) Eq.refl
