{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D364 (W : Ws) where

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
  q6 = wE 673 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 1 W
  q10 : Eqn
  q10 = wE 113 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q12 : Eqn
  q12 = wE 114 W
  q13 : Eqn
  q13 = wE 3 W
  q14 : Eqn
  q14 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q15 : Eqn
  q15 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 630 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part1: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌丘乆並乏丶乏丘並中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中丘乏丼丠乖丼乏丘中中乑业中中中中中中中中中乌中中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part1 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌丘乆並乏丶乏丘並中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丧丧丧乄丧丧乌中中中丘乏丼丠乖丼乏丘中中乑业中中中中中中中中中乌中中中乑中中丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丘乆丘临与临与丠丠丠临与丠丠丠丠丠丠")
  (re 45 3 (ℓ "丽") ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q3 ∷
   rw 46 q4 ∷
   rw 47 q3 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q5 ∷
   rw 41 q6 ∷
   rw 42 q7 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q3 ∷
   rw 41 q8 ∷
   rw⁻ 40 q3 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q3 ∷
   rw 42 q4 ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q5 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q9 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q10 ∷
   rw 43 q11 ∷
   rw 42 q12 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q13 ∷
   re 42 5 (ℓ "中") ∷
   rw 44 q7 ∷
   rw⁻ 43 q2 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q3 ∷
   rw 43 q8 ∷
   rw⁻ 42 q3 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q3 ∷
   rw 44 q4 ∷
   rw 45 q3 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q5 ∷
   rw 41 q7 ∷
   rw⁻ 40 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q3 ∷
   rw 40 q8 ∷
   rw⁻ 39 q3 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q3 ∷
   rw 41 q4 ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q5 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q9 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q10 ∷
   rw 42 q11 ∷
   rw 41 q12 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q13 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q7 ∷
   rw⁻ 42 q2 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q3 ∷
   rw 42 q8 ∷
   rw⁻ 41 q3 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q3 ∷
   rw 43 q4 ∷
   rw 44 q3 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q5 ∷
   rw 40 q7 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q3 ∷
   rw 39 q8 ∷
   rw⁻ 38 q3 ∷
   re 39 3 (ℓ "丽") ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q3 ∷
   rw 40 q4 ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q5 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q9 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   rw 40 q12 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q13 ∷
   re 40 5 (ℓ "中") ∷
   rw 42 q7 ∷
   rw⁻ 41 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q3 ∷
   rw 41 q8 ∷
   rw⁻ 40 q3 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q3 ∷
   rw 42 q4 ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q5 ∷
   rw 39 q7 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q3 ∷
   rw 38 q8 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (ℓ "丽") ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q5 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q9 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   rw 39 q12 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q13 ∷
   re 39 5 (ℓ "中") ∷
   rw 41 q7 ∷
   rw⁻ 40 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q3 ∷
   rw 40 q8 ∷
   rw⁻ 39 q3 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q3 ∷
   rw 41 q4 ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q5 ∷
   rw 38 q7 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q3 ∷
   rw 37 q8 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (ℓ "丽") ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q3 ∷
   rw 38 q4 ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q5 ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q9 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   rw 38 q12 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q13 ∷
   re 38 5 (ℓ "中") ∷
   rw 40 q7 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q3 ∷
   rw 39 q8 ∷
   rw⁻ 38 q3 ∷
   re 39 3 (ℓ "丽") ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q3 ∷
   rw 40 q4 ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q5 ∷
   rw 37 q7 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q8 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q5 ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q9 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q10 ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q13 ∷
   re 37 5 (ℓ "中") ∷
   rw 39 q7 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q3 ∷
   rw 38 q8 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (ℓ "丽") ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q5 ∷
   rw 36 q7 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q8 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "丽") ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q3 ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q5 ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q9 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw 36 q12 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q13 ∷
   re 36 5 (ℓ "中") ∷
   rw 38 q7 ∷
   rw⁻ 37 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw⁻ 38 q3 ∷
   rw 37 q8 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (ℓ "丽") ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q3 ∷
   rw 38 q4 ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q5 ∷
   rw 35 q7 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q8 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   rw 34 q1 ∷
   rw 33 q2 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q5 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q9 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   rw 35 q12 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q13 ∷
   re 35 5 (ℓ "中") ∷
   rw 37 q7 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q8 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q5 ∷
   rw 34 q7 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q8 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q1 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q3 ∷
   rw 34 q4 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q5 ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q9 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   rw 34 q12 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q13 ∷
   re 34 5 (ℓ "中") ∷
   rw 36 q7 ∷
   rw⁻ 35 q2 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q8 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "丽") ∷
   rw 35 q1 ∷
   rw 34 q2 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q3 ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q5 ∷
   rw⁻ 31 q14 ∷
   rw⁻ 32 q15 ∷
   rw⁻ 33 q14 ∷
   rw 32 q7 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q16 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q17 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q3 ∷
   rw 32 q18 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q5 ∷
   re 31 1 (ℓ "乏丼临丼乏") ∷
   rw 37 q9 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q10 ∷
   rw 33 q19 ∷
   rw 32 q12 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q13 ∷
   re 32 5 (ℓ "乑") ∷
   rw 34 q7 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q16 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乔") ∷
   rw 33 q17 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q3 ∷
   rw 34 q18 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q5 ∷
   rw 31 q7 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q8 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q1 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q5 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q9 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   rw 31 q12 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q13 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q7 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q8 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q1 ∷
   rw 31 q2 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q3 ∷
   rw 33 q4 ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q5 ∷
   rw 30 q7 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q8 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q9 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q12 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q13 ∷
   re 30 5 (ℓ "中") ∷
   rw 32 q7 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q8 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q1 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q5 ∷
   rw 29 q7 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q8 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   rw 29 q4 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q5 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q9 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q10 ∷ []) Eq.refl
