{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D363 (W : Ws) where

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
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q8 : Eqn
  q8 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q9 : Eqn
  q9 = wE 985 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 629 W
  q14 : Eqn
  q14 = wE 1 W
  q15 : Eqn
  q15 = wE 113 W
  q16 : Eqn
  q16 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q17 : Eqn
  q17 = wE 114 W
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 630 W
  q20 : Eqn
  q20 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part0: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌丘乆並乏丶乏丘並中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part0 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌丘乆並乏丶乏丘並中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠")
  (rw 48 q1 ∷
   rw⁻ 47 q2 ∷
   rw 46 q3 ∷
   rw 45 q3 ∷
   rw 44 q3 ∷
   rw 43 q3 ∷
   rw 42 q3 ∷
   rw 41 q3 ∷
   rw⁻ 40 q4 ∷
   rw 39 q5 ∷
   rw 38 q3 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   rw 32 q5 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q6 ∷
   rw 31 q3 ∷
   rw⁻ 30 q6 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q6 ∷
   rw 30 q3 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q6 ∷
   rw 29 q5 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q6 ∷
   rw 28 q3 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q6 ∷
   rw 27 q3 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q6 ∷
   rw 26 q3 ∷
   rw⁻ 25 q6 ∷
   re 26 3 (ℓ "丽") ∷
   rw⁻ 24 q7 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q6 ∷
   rw 24 q3 ∷
   rw⁻ 23 q6 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q6 ∷
   rw 23 q3 ∷
   rw⁻ 22 q6 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q6 ∷
   rw 22 q3 ∷
   rw⁻ 21 q6 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q6 ∷
   rw 21 q3 ∷
   rw⁻ 20 q6 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q6 ∷
   rw 20 q3 ∷
   rw⁻ 19 q6 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q6 ∷
   rw 19 q3 ∷
   rw⁻ 18 q6 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q6 ∷
   rw 18 q3 ∷
   rw⁻ 17 q6 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q6 ∷
   rw 17 q3 ∷
   rw⁻ 16 q6 ∷
   re 17 3 (ℓ "丽") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q6 ∷
   rw 16 q3 ∷
   rw⁻ 15 q6 ∷
   re 16 3 (ℓ "丽") ∷
   rw⁻ 14 q8 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q6 ∷
   rw 14 q5 ∷
   rw⁻ 13 q6 ∷
   re 14 3 (ℓ "乔") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q6 ∷
   rw 13 q3 ∷
   rw⁻ 12 q6 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q6 ∷
   rw 12 q3 ∷
   rw⁻ 11 q6 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q6 ∷
   rw 11 q3 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q6 ∷
   rw 10 q3 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q3 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q6 ∷
   rw 8 q3 ∷
   rw⁻ 7 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 6 q7 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q5 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q4 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   rw 7 q11 ∷
   rw 8 q10 ∷
   rw 9 q4 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   rw 12 q11 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q2 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q10 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q7 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q6 ∷
   rw 25 q11 ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q6 ∷
   rw 26 q11 ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q6 ∷
   rw 27 q11 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q6 ∷
   rw 28 q11 ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q6 ∷
   rw 29 q11 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q6 ∷
   rw 30 q11 ∷
   rw 31 q6 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q6 ∷
   rw 31 q10 ∷
   rw 32 q6 ∷
   re 30 3 (ℓ "乑") ∷
   rw 31 q8 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q6 ∷
   rw 33 q11 ∷
   rw 34 q6 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q6 ∷
   rw 34 q11 ∷
   rw 35 q6 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q6 ∷
   rw 35 q11 ∷
   rw 36 q6 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q6 ∷
   rw 36 q11 ∷
   rw 37 q6 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q6 ∷
   rw 37 q11 ∷
   rw 38 q6 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q6 ∷
   rw 38 q11 ∷
   rw 39 q6 ∷
   re 37 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q6 ∷
   rw 39 q11 ∷
   rw 40 q6 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q6 ∷
   rw 40 q11 ∷
   rw 41 q6 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q6 ∷
   rw 41 q11 ∷
   rw 42 q6 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q7 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q6 ∷
   rw 43 q11 ∷
   rw 44 q6 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q6 ∷
   rw 44 q11 ∷
   rw 45 q6 ∷
   re 43 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q6 ∷
   rw 45 q11 ∷
   rw 46 q6 ∷
   re 44 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏乇乏") ∷
   rw 45 q6 ∷
   rw 46 q10 ∷
   rw 47 q6 ∷
   re 45 3 (ℓ "乑") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q6 ∷
   rw 47 q11 ∷
   rw 48 q6 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q6 ∷
   rw 48 q11 ∷
   rw 49 q6 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q12 ∷
   rw 49 q1 ∷
   rw⁻ 48 q2 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q6 ∷
   rw 48 q3 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q13 ∷
   rw 47 q2 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q6 ∷
   rw 49 q11 ∷
   rw 50 q6 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q12 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q14 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q15 ∷
   rw 50 q16 ∷
   rw 49 q17 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q18 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q1 ∷
   rw⁻ 50 q2 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q6 ∷
   rw 50 q3 ∷
   rw⁻ 49 q6 ∷
   re 50 3 (ℓ "丽") ∷
   rw 50 q13 ∷
   rw 49 q2 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q6 ∷
   rw 51 q11 ∷
   rw 52 q6 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q12 ∷
   rw 48 q1 ∷
   rw⁻ 47 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q6 ∷
   rw 47 q3 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q13 ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q6 ∷
   rw 48 q11 ∷
   rw 49 q6 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q12 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q14 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q15 ∷
   rw 49 q16 ∷
   rw 48 q17 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q18 ∷
   re 48 5 (ℓ "中") ∷
   rw 50 q1 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q6 ∷
   rw 49 q3 ∷
   rw⁻ 48 q6 ∷
   re 49 3 (ℓ "丽") ∷
   rw 49 q13 ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q6 ∷
   rw 50 q11 ∷
   rw 51 q6 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q12 ∷
   rw 47 q1 ∷
   rw⁻ 46 q2 ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw⁻ 47 q6 ∷
   rw 46 q5 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (ℓ "乔") ∷
   rw 46 q19 ∷
   rw 45 q2 ∷
   re 47 1 (ℓ "乏乇乏") ∷
   rw 46 q6 ∷
   rw 47 q10 ∷
   rw 48 q6 ∷
   re 46 3 (ℓ "乑") ∷
   rw 47 q12 ∷
   re 46 1 (ℓ "乏丼临丼乏") ∷
   rw 52 q14 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q15 ∷
   rw 48 q20 ∷
   rw 47 q17 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q18 ∷
   re 47 5 (ℓ "乑") ∷
   rw 49 q1 ∷
   rw⁻ 48 q2 ∷
   re 47 1 (ℓ "乏乄乏") ∷
   rw⁻ 49 q6 ∷
   rw 48 q5 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (ℓ "乔") ∷
   rw 48 q19 ∷
   rw 47 q2 ∷
   re 49 1 (ℓ "乏乇乏") ∷
   rw 48 q6 ∷
   rw 49 q10 ∷
   rw 50 q6 ∷
   re 48 3 (ℓ "乑") ∷
   rw 49 q12 ∷
   rw 46 q1 ∷
   rw⁻ 45 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q6 ∷
   rw 45 q3 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q13 ∷
   rw 44 q2 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q6 ∷
   rw 46 q11 ∷
   rw 47 q6 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q12 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q14 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q15 ∷
   rw 47 q16 ∷
   rw 46 q17 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q18 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q1 ∷
   rw⁻ 47 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q6 ∷
   rw 47 q3 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q13 ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q6 ∷
   rw 48 q11 ∷
   rw 49 q6 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q12 ∷
   rw 45 q1 ∷
   rw⁻ 44 q2 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q6 ∷
   rw 44 q3 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q13 ∷
   rw 43 q2 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q6 ∷
   rw 45 q11 ∷
   rw 46 q6 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q12 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q14 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q15 ∷
   rw 46 q16 ∷
   rw 45 q17 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q18 ∷
   re 45 5 (ℓ "中") ∷
   rw 47 q1 ∷
   rw⁻ 46 q2 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q6 ∷
   rw 46 q3 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q13 ∷
   rw 45 q2 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q6 ∷
   rw 47 q11 ∷
   rw 48 q6 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q12 ∷
   rw 44 q1 ∷
   rw⁻ 43 q2 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q6 ∷
   rw 43 q3 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q13 ∷
   rw 42 q2 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q6 ∷
   rw 44 q11 ∷
   rw 45 q6 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q12 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q14 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q15 ∷
   rw 45 q16 ∷
   rw 44 q17 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q18 ∷
   re 44 5 (ℓ "中") ∷
   rw 46 q1 ∷
   rw⁻ 45 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q6 ∷
   rw 45 q3 ∷
   rw⁻ 44 q6 ∷ []) Eq.refl
