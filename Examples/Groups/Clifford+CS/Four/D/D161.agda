{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D161 (W : Ws) where

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
  q1 = wE 629 W
  q2 : Eqn
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 27 W
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 113 W
  q8 : Eqn
  q8 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q9 : Eqn
  q9 = wE 114 W
  q10 : Eqn
  q10 = wE 3 W
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = wE 7 W
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
  q21 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q24 : Eqn
  q24 = wE 489 W
  q25 : Eqn
  q25 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q26 : Eqn
  q26 = eqn (ℓ "丏乌") (ℓ "乌丏") (low-comm (((S • S • S) ↑)) (CX₀₁))
  q27 : Eqn
  q27 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q28 : Eqn
  q28 = wE 464 W
  q29 : Eqn
  q29 = wE 490 W
  q30 : Eqn
  q30 = wE 151 W

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part7: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part7 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中並丽丘並乆丘中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乆丘乏丧並乏並乑中乑乑丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part7 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧乄丧乄乄乌乑业乑业中並丽丘並乆丘中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乆丘乏丧並乏並乑中乑乑丘丨久丨丨丘丘丨丨丨丘")
  (rw 52 q1 ∷
   rw 51 q2 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q5 ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q6 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q7 ∷
   rw 54 q8 ∷
   rw 53 q9 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q10 ∷
   re 53 5 (ℓ "中") ∷
   rw 55 q11 ∷
   rw⁻ 54 q2 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q3 ∷
   rw 54 q12 ∷
   rw⁻ 53 q3 ∷
   re 54 3 (ℓ "丽") ∷
   rw 54 q1 ∷
   rw 53 q2 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q3 ∷
   rw 55 q4 ∷
   rw 56 q3 ∷
   re 54 3 (ℓ "中") ∷
   rw 55 q5 ∷
   rw 52 q11 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q3 ∷
   rw 51 q12 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (ℓ "丽") ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q3 ∷
   rw 52 q4 ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q5 ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q6 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q7 ∷
   rw 53 q8 ∷
   rw 52 q9 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q10 ∷
   re 52 5 (ℓ "中") ∷
   rw 54 q11 ∷
   rw⁻ 53 q2 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q3 ∷
   rw 53 q12 ∷
   rw⁻ 52 q3 ∷
   re 53 3 (ℓ "丽") ∷
   rw 53 q1 ∷
   rw 52 q2 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q3 ∷
   rw 54 q4 ∷
   rw 55 q3 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q5 ∷
   rw⁻ 49 q13 ∷
   rw⁻ 50 q14 ∷
   rw⁻ 51 q13 ∷
   rw 50 q11 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw⁻ 50 q3 ∷
   rw 49 q15 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (ℓ "乔") ∷
   rw 49 q16 ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q3 ∷
   rw 50 q17 ∷
   rw 51 q3 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q5 ∷
   re 49 1 (ℓ "乏丼临丼乏") ∷
   rw 55 q6 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q7 ∷
   rw 51 q18 ∷
   rw 50 q9 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q10 ∷
   re 50 5 (ℓ "乑") ∷
   rw 52 q11 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (ℓ "乏乄乏") ∷
   rw⁻ 52 q3 ∷
   rw 51 q15 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (ℓ "乔") ∷
   rw 51 q16 ∷
   rw 50 q2 ∷
   re 52 1 (ℓ "乏乇乏") ∷
   rw 51 q3 ∷
   rw 52 q17 ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "乑") ∷
   rw 52 q5 ∷
   rw⁻ 47 q13 ∷
   rw⁻ 48 q14 ∷
   rw⁻ 49 q13 ∷
   rw 48 q11 ∷
   rw⁻ 47 q2 ∷
   re 46 1 (ℓ "乏乄乏") ∷
   rw⁻ 48 q3 ∷
   rw 47 q15 ∷
   rw⁻ 46 q3 ∷
   re 47 3 (ℓ "乔") ∷
   rw 47 q16 ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏乇乏") ∷
   rw 47 q3 ∷
   rw 48 q17 ∷
   rw 49 q3 ∷
   re 47 3 (ℓ "乑") ∷
   rw 48 q5 ∷
   re 47 1 (ℓ "乏丼临丼乏") ∷
   rw 53 q6 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q7 ∷
   rw 49 q18 ∷
   rw 48 q9 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q10 ∷
   re 48 5 (ℓ "乑") ∷
   rw 50 q11 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw⁻ 50 q3 ∷
   rw 49 q15 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (ℓ "乔") ∷
   rw 49 q16 ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q3 ∷
   rw 50 q17 ∷
   rw 51 q3 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q5 ∷
   rw 45 q19 ∷
   rw 39 q20 ∷
   rw 82 q6 ∷
   rw 81 q21 ∷
   rw 80 q21 ∷
   rw 79 q21 ∷
   rw 78 q22 ∷
   rw 77 q23 ∷
   rw 76 q21 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   rw 72 q21 ∷
   rw 71 q21 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q10 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw 71 q10 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q10 ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw 69 q10 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q10 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q10 ∷
   rw 66 q24 ∷
   rw⁻ 65 q21 ∷
   rw⁻ 66 q21 ∷
   rw⁻ 67 q21 ∷
   rw⁻ 68 q21 ∷
   rw⁻ 69 q21 ∷
   rw⁻ 70 q21 ∷
   rw⁻ 71 q23 ∷
   rw⁻ 72 q22 ∷
   rw⁻ 73 q21 ∷
   rw⁻ 74 q21 ∷
   rw⁻ 75 q21 ∷
   rw 78 q6 ∷
   re 76 3 (ℓ "中") ∷
   rw 79 q6 ∷
   re 77 3 (ℓ "中") ∷
   rw 80 q6 ∷
   re 78 3 (ℓ "乑") ∷
   rw 81 q6 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q6 ∷
   re 80 3 (ℓ "乑") ∷
   rw 83 q6 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q10 ∷
   rw⁻ 64 q25 ∷
   rw⁻ 65 q25 ∷
   rw⁻ 66 q25 ∷
   rw⁻ 67 q25 ∷
   rw⁻ 68 q25 ∷
   rw⁻ 69 q25 ∷
   rw⁻ 70 q26 ∷
   rw⁻ 71 q27 ∷
   rw⁻ 72 q25 ∷
   rw⁻ 73 q25 ∷
   rw⁻ 74 q25 ∷
   rw 75 q6 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   rw 72 q21 ∷
   rw 71 q22 ∷
   rw 70 q23 ∷
   rw 69 q21 ∷
   rw 68 q21 ∷
   rw 67 q21 ∷
   rw 66 q21 ∷
   rw 65 q21 ∷
   rw 64 q21 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q10 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q10 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q10 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q10 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q10 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q10 ∷
   rw 57 q28 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q10 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q10 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q10 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q10 ∷
   rw 52 q28 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw 53 q10 ∷
   rw 50 q28 ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw 51 q10 ∷
   rw 50 q29 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q21 ∷
   rw⁻ 51 q21 ∷
   rw⁻ 52 q21 ∷
   rw⁻ 53 q21 ∷
   rw⁻ 54 q21 ∷
   rw⁻ 55 q23 ∷
   rw⁻ 56 q22 ∷
   rw⁻ 57 q21 ∷
   rw⁻ 58 q21 ∷
   rw⁻ 59 q21 ∷
   rw 62 q6 ∷
   re 60 3 (ℓ "乑") ∷
   rw 61 q30 ∷
   rw 64 q6 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q30 ∷
   rw 66 q6 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q6 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q6 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q6 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q30 ∷
   rw 71 q6 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q6 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q6 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q6 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q6 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q6 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q10 ∷
   rw⁻ 48 q25 ∷
   rw⁻ 49 q25 ∷
   rw⁻ 50 q25 ∷
   rw⁻ 51 q25 ∷
   rw⁻ 52 q25 ∷
   rw⁻ 53 q25 ∷
   rw⁻ 54 q26 ∷
   rw⁻ 55 q27 ∷
   rw⁻ 56 q25 ∷
   rw⁻ 57 q25 ∷
   rw⁻ 58 q25 ∷
   rw 42 q24 ∷
   rw 83 q11 ∷
   rw⁻ 82 q2 ∷
   re 81 1 (ℓ "乏乄乏") ∷
   rw⁻ 83 q3 ∷
   rw 82 q15 ∷
   rw⁻ 81 q3 ∷
   re 82 3 (ℓ "乔") ∷
   rw 82 q16 ∷
   rw 81 q2 ∷
   re 83 1 (ℓ "乏乇乏") ∷
   rw 82 q3 ∷
   rw 83 q17 ∷
   rw 84 q3 ∷
   re 82 3 (ℓ "乑") ∷
   rw 83 q5 ∷
   re 82 1 (ℓ "乏丼临丼乏") ∷
   rw 88 q6 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q7 ∷
   rw 84 q18 ∷
   rw 83 q9 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q10 ∷
   re 83 5 (ℓ "乑") ∷
   rw 85 q11 ∷
   rw⁻ 84 q2 ∷
   re 83 1 (ℓ "乏乄乏") ∷
   rw⁻ 85 q3 ∷
   rw 84 q15 ∷
   rw⁻ 83 q3 ∷
   re 84 3 (ℓ "乔") ∷
   rw 84 q16 ∷
   rw 83 q2 ∷
   re 85 1 (ℓ "乏乇乏") ∷
   rw 84 q3 ∷
   rw 85 q17 ∷
   rw 86 q3 ∷
   re 84 3 (ℓ "乑") ∷
   rw 85 q5 ∷
   rw 82 q11 ∷
   rw⁻ 81 q2 ∷
   re 80 1 (ℓ "乏乄乏") ∷
   rw⁻ 82 q3 ∷
   rw 81 q15 ∷
   rw⁻ 80 q3 ∷
   re 81 3 (ℓ "乔") ∷
   rw 81 q16 ∷
   rw 80 q2 ∷
   re 82 1 (ℓ "乏乇乏") ∷
   rw 81 q3 ∷
   rw 82 q17 ∷
   rw 83 q3 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q5 ∷
   re 81 1 (ℓ "乏丼临丼乏") ∷
   rw 87 q6 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q7 ∷
   rw 83 q18 ∷
   rw 82 q9 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q10 ∷
   re 82 5 (ℓ "乑") ∷
   rw 84 q11 ∷
   rw⁻ 83 q2 ∷
   re 82 1 (ℓ "乏乄乏") ∷
   rw⁻ 84 q3 ∷
   rw 83 q15 ∷
   rw⁻ 82 q3 ∷
   re 83 3 (ℓ "乔") ∷
   rw 83 q16 ∷
   rw 82 q2 ∷
   re 84 1 (ℓ "乏乇乏") ∷
   rw 83 q3 ∷
   rw 84 q17 ∷
   rw 85 q3 ∷
   re 83 3 (ℓ "乑") ∷
   rw 84 q5 ∷
   rw 81 q11 ∷
   rw⁻ 80 q2 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q3 ∷
   rw 80 q12 ∷
   rw⁻ 79 q3 ∷
   re 80 3 (ℓ "丽") ∷
   rw 80 q1 ∷
   rw 79 q2 ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q3 ∷
   rw 81 q4 ∷
   rw 82 q3 ∷
   re 80 3 (ℓ "中") ∷
   rw 81 q5 ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q6 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q7 ∷
   rw 82 q8 ∷
   rw 81 q9 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q10 ∷
   re 81 5 (ℓ "中") ∷
   rw 83 q11 ∷
   rw⁻ 82 q2 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q3 ∷
   rw 82 q12 ∷
   rw⁻ 81 q3 ∷
   re 82 3 (ℓ "丽") ∷
   rw 82 q1 ∷
   rw 81 q2 ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q3 ∷
   rw 83 q4 ∷
   rw 84 q3 ∷
   re 82 3 (ℓ "中") ∷
   rw 83 q5 ∷
   rw 80 q11 ∷
   rw⁻ 79 q2 ∷
   re 78 1 (ℓ "乏乄乏") ∷
   rw⁻ 80 q3 ∷
   rw 79 q15 ∷
   rw⁻ 78 q3 ∷
   re 79 3 (ℓ "乔") ∷
   rw 79 q16 ∷
   rw 78 q2 ∷
   re 80 1 (ℓ "乏乇乏") ∷
   rw 79 q3 ∷
   rw 80 q17 ∷
   rw 81 q3 ∷
   re 79 3 (ℓ "乑") ∷
   rw 80 q5 ∷
   re 79 1 (ℓ "乏丼临丼乏") ∷
   rw 85 q6 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q7 ∷
   rw 81 q18 ∷
   rw 80 q9 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q10 ∷
   re 80 5 (ℓ "乑") ∷
   rw 82 q11 ∷
   rw⁻ 81 q2 ∷
   re 80 1 (ℓ "乏乄乏") ∷
   rw⁻ 82 q3 ∷
   rw 81 q15 ∷
   rw⁻ 80 q3 ∷
   re 81 3 (ℓ "乔") ∷
   rw 81 q16 ∷
   rw 80 q2 ∷
   re 82 1 (ℓ "乏乇乏") ∷
   rw 81 q3 ∷
   rw 82 q17 ∷
   rw 83 q3 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q5 ∷
   rw 79 q11 ∷
   rw⁻ 78 q2 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q3 ∷
   rw 78 q12 ∷
   rw⁻ 77 q3 ∷
   re 78 3 (ℓ "丽") ∷
   rw 78 q1 ∷
   rw 77 q2 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q3 ∷
   rw 79 q4 ∷
   rw 80 q3 ∷
   re 78 3 (ℓ "中") ∷
   rw 79 q5 ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q6 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q7 ∷
   rw 80 q8 ∷
   rw 79 q9 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q10 ∷
   re 79 5 (ℓ "中") ∷
   rw 81 q11 ∷
   rw⁻ 80 q2 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q3 ∷
   rw 80 q12 ∷
   rw⁻ 79 q3 ∷
   re 80 3 (ℓ "丽") ∷
   rw 80 q1 ∷
   rw 79 q2 ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q3 ∷
   rw 81 q4 ∷ []) Eq.refl
