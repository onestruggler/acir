{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D083 (W : Ws) where

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
  q1 = wE 611 W
  q2 : Eqn
  q2 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q3 : Eqn
  q3 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q4 : Eqn
  q4 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q5 : Eqn
  q5 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = wE 612 W
  q7 : Eqn
  q7 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q8 : Eqn
  q8 = eqn (ℓ "与乌") (ℓ "乌与") (low-comm ((S ↑)) (CX₀₁))
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q11 : Eqn
  q11 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q12 : Eqn
  q12 = wE 140 W
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 613 W
  q15 : Eqn
  q15 = wE 27 W
  q16 : Eqn
  q16 = wE 142 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = wE 464 W
  q20 : Eqn
  q20 = wE 3 W
  q21 : Eqn
  q21 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q23 : Eqn
  q23 = wE 614 W
  q24 : Eqn
  q24 = wE 151 W
  q25 : Eqn
  q25 = wE 13 W
  q26 : Eqn
  q26 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q27 : Eqn
  q27 = wE 78 W
  q28 : Eqn
  q28 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))
  q29 : Eqn
  q29 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSKSKK;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part0: 500 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part0 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丘乌丘乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中乏丼丠丼乏乆乏乏业业业乑业业业业乑业丠丠临丠临临丘乌丘乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part0 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乑业丘乌丘乑业乑业中中中乑业中中中中中中") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中乏丼丠丼乏乆乏乏业业业乑业业业业乑业丠丠临丠临临丘乌丘乑业乑业中中中乑业中中中中中中")
  (rw 0 q1 ∷
   rw 45 q2 ∷
   rw 46 q3 ∷
   rw 47 q2 ∷
   rw 44 q2 ∷
   rw 45 q3 ∷
   rw 46 q2 ∷
   rw 43 q4 ∷
   rw 44 q5 ∷
   rw 45 q4 ∷
   rw 42 q2 ∷
   rw 43 q3 ∷
   rw 44 q2 ∷
   rw 41 q4 ∷
   rw 42 q5 ∷
   rw 43 q4 ∷
   rw 40 q4 ∷
   rw 41 q5 ∷
   rw 42 q4 ∷
   rw 39 q6 ∷
   rw 38 q4 ∷
   rw 39 q5 ∷
   rw 40 q4 ∷
   rw 37 q4 ∷
   rw 38 q5 ∷
   rw 39 q4 ∷
   rw 36 q4 ∷
   rw 37 q5 ∷
   rw 38 q4 ∷
   rw 35 q4 ∷
   rw 36 q5 ∷
   rw 37 q4 ∷
   rw 34 q4 ∷
   rw 35 q5 ∷
   rw 36 q4 ∷
   rw 33 q4 ∷
   rw 34 q5 ∷
   rw 35 q4 ∷
   rw 32 q7 ∷
   rw 33 q8 ∷
   rw 34 q7 ∷
   rw 31 q2 ∷
   rw 32 q3 ∷
   rw 33 q2 ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw 32 q4 ∷
   rw 29 q4 ∷
   rw 30 q5 ∷
   rw 31 q4 ∷
   rw 28 q4 ∷
   rw 29 q5 ∷
   rw 30 q4 ∷
   rw 27 q7 ∷
   rw 28 q8 ∷
   rw 29 q7 ∷
   rw 26 q2 ∷
   rw 27 q3 ∷
   rw 28 q2 ∷
   rw 25 q7 ∷
   rw 26 q8 ∷
   rw 27 q7 ∷
   rw 24 q2 ∷
   rw 25 q3 ∷
   rw 26 q2 ∷
   rw 23 q6 ∷
   rw 26 q9 ∷
   rw⁻ 25 q10 ∷
   rw⁻ 24 q11 ∷
   rw⁻ 23 q10 ∷
   rw 22 q12 ∷
   rw 21 q12 ∷
   rw 20 q13 ∷
   rw 19 q12 ∷
   rw 18 q13 ∷
   rw 17 q13 ∷
   rw 18 q14 ∷
   rw 17 q10 ∷
   rw 18 q11 ∷
   rw 19 q10 ∷
   rw 20 q15 ∷
   rw 21 q15 ∷
   rw 22 q16 ∷
   rw 23 q15 ∷
   rw 24 q16 ∷
   rw 25 q16 ∷
   rw 26 q17 ∷
   rw 91 q18 ∷
   rw 90 q19 ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw 91 q20 ∷
   rw 88 q19 ∷
   rw 87 q19 ∷
   rw 86 q19 ∷
   rw 85 q19 ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw 86 q20 ∷
   rw 83 q19 ∷
   rw 82 q19 ∷
   rw 81 q19 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q20 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q20 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q20 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q20 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q20 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q20 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q20 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q20 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q20 ∷
   rw 71 q19 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q20 ∷
   rw 69 q19 ∷
   rw 68 q19 ∷
   rw 67 q19 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q20 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q20 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q20 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q20 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q20 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q20 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q20 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q20 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q20 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q20 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q20 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q20 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q20 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q20 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q20 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q20 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q20 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q20 ∷
   rw 48 q21 ∷
   rw 47 q21 ∷
   rw 46 q22 ∷
   rw 45 q21 ∷
   rw 44 q22 ∷
   rw 43 q22 ∷
   rw 44 q23 ∷
   rw 45 q18 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q18 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q18 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q18 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q18 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q18 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q18 ∷
   re 49 3 (ℓ "中") ∷
   rw 52 q18 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q18 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q18 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q18 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q18 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q18 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q18 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q18 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q18 ∷
   re 58 3 (ℓ "中") ∷
   rw 61 q18 ∷
   re 59 3 (ℓ "中") ∷
   rw 62 q18 ∷
   re 60 3 (ℓ "中") ∷
   rw 61 q24 ∷
   rw 62 q24 ∷
   rw 63 q24 ∷
   rw 66 q18 ∷
   re 64 3 (ℓ "乑") ∷
   rw 65 q24 ∷
   rw 68 q18 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q18 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q18 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q18 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q18 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q18 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q18 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q18 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q18 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q24 ∷
   rw 76 q24 ∷
   rw 77 q24 ∷
   rw 80 q18 ∷
   re 78 3 (ℓ "乑") ∷
   rw 79 q24 ∷
   rw 80 q24 ∷
   rw 81 q24 ∷
   rw 82 q24 ∷
   rw 85 q18 ∷
   re 83 3 (ℓ "乑") ∷
   rw 84 q24 ∷
   rw⁻ 85 q22 ∷
   rw⁻ 86 q22 ∷
   rw⁻ 87 q21 ∷
   rw⁻ 88 q22 ∷
   rw⁻ 89 q21 ∷
   rw⁻ 90 q21 ∷
   rw 91 q20 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q18 ∷
   re 43 3 (ℓ "乓") ∷
   rw 43 q25 ∷
   rw⁻ 44 q26 ∷
   rw 45 q27 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q20 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q18 ∷
   re 44 3 (ℓ "乓") ∷
   rw 44 q25 ∷
   rw⁻ 45 q26 ∷
   rw 46 q27 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 49 q20 ∷
   re 43 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q18 ∷
   re 45 3 (ℓ "乓") ∷
   rw 45 q25 ∷
   rw⁻ 46 q26 ∷
   rw 47 q27 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 50 q20 ∷
   re 44 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q18 ∷
   re 46 3 (ℓ "乓") ∷
   rw 46 q25 ∷
   rw⁻ 47 q26 ∷
   rw 48 q27 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 51 q20 ∷
   re 45 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q18 ∷
   re 47 3 (ℓ "乓") ∷
   rw 47 q25 ∷
   rw⁻ 48 q26 ∷
   rw 49 q27 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 52 q20 ∷
   re 46 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q18 ∷
   re 48 3 (ℓ "乓") ∷
   rw 48 q25 ∷
   rw⁻ 49 q26 ∷
   rw 50 q27 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 53 q20 ∷
   re 47 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q18 ∷
   re 49 3 (ℓ "乓") ∷
   rw 49 q25 ∷
   rw⁻ 50 q26 ∷
   rw 51 q27 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 54 q20 ∷
   re 48 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q18 ∷
   re 50 3 (ℓ "乓") ∷
   rw 50 q25 ∷
   rw⁻ 51 q26 ∷
   rw 52 q27 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 55 q20 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q18 ∷
   re 51 3 (ℓ "乓") ∷
   rw 51 q25 ∷
   rw⁻ 52 q26 ∷
   rw 53 q27 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q20 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q18 ∷
   re 52 3 (ℓ "乓") ∷
   rw 52 q25 ∷
   rw⁻ 53 q26 ∷
   rw 54 q27 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 57 q20 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q18 ∷
   re 53 3 (ℓ "乓") ∷
   rw 53 q25 ∷
   rw⁻ 54 q26 ∷
   rw 55 q27 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 58 q20 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q18 ∷
   re 54 3 (ℓ "乓") ∷
   rw 54 q25 ∷
   rw⁻ 55 q26 ∷
   rw 56 q27 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 59 q20 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q18 ∷
   re 55 3 (ℓ "乓") ∷
   rw 55 q25 ∷
   rw⁻ 56 q26 ∷
   rw 57 q27 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 60 q20 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q18 ∷
   re 56 3 (ℓ "乓") ∷
   rw 56 q25 ∷
   rw⁻ 57 q26 ∷
   rw 58 q27 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 61 q20 ∷
   re 55 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q18 ∷
   re 57 3 (ℓ "乓") ∷
   rw 57 q25 ∷
   rw⁻ 58 q26 ∷
   rw 59 q27 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 62 q20 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q18 ∷
   re 58 3 (ℓ "乓") ∷
   rw 58 q25 ∷
   rw⁻ 59 q26 ∷
   rw 60 q27 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 63 q20 ∷
   re 57 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q18 ∷
   re 59 3 (ℓ "乓") ∷
   rw 59 q25 ∷
   rw⁻ 60 q26 ∷
   rw 61 q27 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 64 q20 ∷
   re 58 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q18 ∷
   re 60 3 (ℓ "乓") ∷
   rw 60 q25 ∷
   rw⁻ 61 q26 ∷
   rw 62 q27 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 65 q20 ∷
   re 59 5 (ℓ "中") ∷
   rw 60 q28 ∷
   rw 61 q28 ∷
   rw 62 q28 ∷
   re 64 1 (ℓ "乏丼临丼乏") ∷
   rw 63 q18 ∷
   re 64 3 (ℓ "乓") ∷
   rw 64 q25 ∷
   rw⁻ 65 q29 ∷
   rw 66 q27 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 69 q20 ∷
   re 63 5 (ℓ "乑") ∷
   rw 64 q28 ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q18 ∷
   re 66 3 (ℓ "乓") ∷
   rw 66 q25 ∷
   rw⁻ 67 q26 ∷
   rw 68 q27 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 71 q20 ∷
   re 65 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q18 ∷
   re 67 3 (ℓ "乓") ∷
   rw 67 q25 ∷
   rw⁻ 68 q26 ∷
   rw 69 q27 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 72 q20 ∷
   re 66 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q18 ∷
   re 68 3 (ℓ "乓") ∷
   rw 68 q25 ∷
   rw⁻ 69 q26 ∷
   rw 70 q27 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 73 q20 ∷
   re 67 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q18 ∷
   re 69 3 (ℓ "乓") ∷
   rw 69 q25 ∷
   rw⁻ 70 q26 ∷
   rw 71 q27 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 74 q20 ∷
   re 68 5 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q18 ∷
   re 70 3 (ℓ "乓") ∷
   rw 70 q25 ∷
   rw⁻ 71 q26 ∷
   rw 72 q27 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 75 q20 ∷
   re 69 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q18 ∷
   re 71 3 (ℓ "乓") ∷
   rw 71 q25 ∷
   rw⁻ 72 q26 ∷
   rw 73 q27 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 76 q20 ∷
   re 70 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q18 ∷
   re 72 3 (ℓ "乓") ∷
   rw 72 q25 ∷
   rw⁻ 73 q26 ∷
   rw 74 q27 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 77 q20 ∷
   re 71 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q18 ∷
   re 73 3 (ℓ "乓") ∷
   rw 73 q25 ∷
   rw⁻ 74 q26 ∷
   rw 75 q27 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 78 q20 ∷
   re 72 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q18 ∷
   re 74 3 (ℓ "乓") ∷
   rw 74 q25 ∷
   rw⁻ 75 q26 ∷
   rw 76 q27 ∷
   re 77 1 (ℓ "乏乆乏") ∷ []) Eq.refl
