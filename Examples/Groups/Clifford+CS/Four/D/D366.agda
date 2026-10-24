{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D366 (W : Ws) where

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
  q2 = wE 31 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 113 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q6 : Eqn
  q6 = wE 114 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 5 W
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = wE 629 W
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = wE 630 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q17 : Eqn
  q17 = wE 673 W

-- Bar(SSSKSS;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part3: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中丘乏丧並乏並乆丘临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中乏丧並乏丘並乆丘中中中中中中中乌中中中乑中中临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中丘乏丧並乏並乆丘临与临与丠丠丠临与丠丠丠丠丠丠") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧丧乄丧丧乌中中中中中中乑业中乏丧並乏丘並乆丘中中中中中中中乌中中中乑中中临与临与丠丠丠临与丠丠丠丠丠丠")
  (rw 95 q1 ∷
   re 93 3 (ℓ "中") ∷
   rw 94 q2 ∷
   re 93 1 (ℓ "乏丼丠丼乏") ∷
   rw 99 q3 ∷
   re 97 3 (ℓ "乓") ∷
   rw 96 q4 ∷
   rw 95 q5 ∷
   rw 94 q6 ∷
   re 94 1 (ℓ "乏乆乏") ∷
   rw 93 q7 ∷
   re 94 5 (ℓ "中") ∷
   rw 96 q8 ∷
   rw⁻ 95 q9 ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw⁻ 96 q1 ∷
   rw 95 q10 ∷
   rw⁻ 94 q1 ∷
   re 95 3 (ℓ "丽") ∷
   rw 95 q11 ∷
   rw 94 q9 ∷
   re 96 1 (ℓ "乏丶乏") ∷
   rw 95 q1 ∷
   rw 96 q12 ∷
   rw 97 q1 ∷
   re 95 3 (ℓ "中") ∷
   rw 96 q2 ∷
   rw 93 q8 ∷
   rw⁻ 92 q9 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw⁻ 93 q1 ∷
   rw 92 q10 ∷
   rw⁻ 91 q1 ∷
   re 92 3 (ℓ "丽") ∷
   rw 92 q11 ∷
   rw 91 q9 ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q1 ∷
   rw 93 q12 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "中") ∷
   rw 93 q2 ∷
   re 92 1 (ℓ "乏丼丠丼乏") ∷
   rw 98 q3 ∷
   re 96 3 (ℓ "乓") ∷
   rw 95 q4 ∷
   rw 94 q5 ∷
   rw 93 q6 ∷
   re 93 1 (ℓ "乏乆乏") ∷
   rw 92 q7 ∷
   re 93 5 (ℓ "中") ∷
   rw 95 q8 ∷
   rw⁻ 94 q9 ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw⁻ 95 q1 ∷
   rw 94 q10 ∷
   rw⁻ 93 q1 ∷
   re 94 3 (ℓ "丽") ∷
   rw 94 q11 ∷
   rw 93 q9 ∷
   re 95 1 (ℓ "乏丶乏") ∷
   rw 94 q1 ∷
   rw 95 q12 ∷
   rw 96 q1 ∷
   re 94 3 (ℓ "中") ∷
   rw 95 q2 ∷
   rw 92 q8 ∷
   rw⁻ 91 q9 ∷
   re 90 1 (ℓ "乏乄乏") ∷
   rw⁻ 92 q1 ∷
   rw 91 q13 ∷
   rw⁻ 90 q1 ∷
   re 91 3 (ℓ "乔") ∷
   rw 91 q14 ∷
   rw 90 q9 ∷
   re 92 1 (ℓ "乏乇乏") ∷
   rw 91 q1 ∷
   rw 92 q15 ∷
   rw 93 q1 ∷
   re 91 3 (ℓ "乑") ∷
   rw 92 q2 ∷
   re 91 1 (ℓ "乏丼临丼乏") ∷
   rw 97 q3 ∷
   re 95 3 (ℓ "乓") ∷
   rw 94 q4 ∷
   rw 93 q16 ∷
   rw 92 q6 ∷
   re 92 1 (ℓ "乏乆乏") ∷
   rw 91 q7 ∷
   re 92 5 (ℓ "乑") ∷
   rw 94 q8 ∷
   rw⁻ 93 q9 ∷
   re 92 1 (ℓ "乏乄乏") ∷
   rw⁻ 94 q1 ∷
   rw 93 q13 ∷
   rw⁻ 92 q1 ∷
   re 93 3 (ℓ "乔") ∷
   rw 93 q14 ∷
   rw 92 q9 ∷
   re 94 1 (ℓ "乏乇乏") ∷
   rw 93 q1 ∷
   rw 94 q15 ∷
   rw 95 q1 ∷
   re 93 3 (ℓ "乑") ∷
   rw 94 q2 ∷
   rw 91 q8 ∷
   rw⁻ 90 q9 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw⁻ 91 q1 ∷
   rw 90 q10 ∷
   rw⁻ 89 q1 ∷
   re 90 3 (ℓ "丽") ∷
   rw 90 q11 ∷
   rw 89 q9 ∷
   re 91 1 (ℓ "乏丶乏") ∷
   rw 90 q1 ∷
   rw 91 q12 ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "中") ∷
   rw 91 q2 ∷
   re 90 1 (ℓ "乏丼丠丼乏") ∷
   rw 96 q3 ∷
   re 94 3 (ℓ "乓") ∷
   rw 93 q4 ∷
   rw 92 q5 ∷
   rw 91 q6 ∷
   re 91 1 (ℓ "乏乆乏") ∷
   rw 90 q7 ∷
   re 91 5 (ℓ "中") ∷
   rw 93 q8 ∷
   rw⁻ 92 q9 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw⁻ 93 q1 ∷
   rw 92 q10 ∷
   rw⁻ 91 q1 ∷
   re 92 3 (ℓ "丽") ∷
   rw 92 q11 ∷
   rw 91 q9 ∷
   re 93 1 (ℓ "乏丶乏") ∷
   rw 92 q1 ∷
   rw 93 q12 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "中") ∷
   rw 93 q2 ∷
   rw 90 q8 ∷
   rw⁻ 89 q9 ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw⁻ 90 q1 ∷
   rw 89 q10 ∷
   rw⁻ 88 q1 ∷
   re 89 3 (ℓ "丽") ∷
   rw 89 q11 ∷
   rw 88 q9 ∷
   re 90 1 (ℓ "乏丶乏") ∷
   rw 89 q1 ∷
   rw 90 q12 ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "中") ∷
   rw 90 q2 ∷
   re 89 1 (ℓ "乏丼丠丼乏") ∷
   rw 95 q3 ∷
   re 93 3 (ℓ "乓") ∷
   rw 92 q4 ∷
   rw 91 q5 ∷
   rw 90 q6 ∷
   re 90 1 (ℓ "乏乆乏") ∷
   rw 89 q7 ∷
   re 90 5 (ℓ "中") ∷
   rw 92 q8 ∷
   rw⁻ 91 q9 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw⁻ 92 q1 ∷
   rw 91 q10 ∷
   rw⁻ 90 q1 ∷
   re 91 3 (ℓ "丽") ∷
   rw 91 q11 ∷
   rw 90 q9 ∷
   re 92 1 (ℓ "乏丶乏") ∷
   rw 91 q1 ∷
   rw 92 q12 ∷
   rw 93 q1 ∷
   re 91 3 (ℓ "中") ∷
   rw 92 q2 ∷
   rw 89 q8 ∷
   rw⁻ 88 q9 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw⁻ 89 q1 ∷
   rw 88 q10 ∷
   rw⁻ 87 q1 ∷
   re 88 3 (ℓ "丽") ∷
   rw 88 q11 ∷
   rw 87 q9 ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q1 ∷
   rw 89 q12 ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "中") ∷
   rw 89 q2 ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 94 q3 ∷
   re 92 3 (ℓ "乓") ∷
   rw 91 q4 ∷
   rw 90 q5 ∷
   rw 89 q6 ∷
   re 89 1 (ℓ "乏乆乏") ∷
   rw 88 q7 ∷
   re 89 5 (ℓ "中") ∷
   rw 91 q8 ∷
   rw⁻ 90 q9 ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw⁻ 91 q1 ∷
   rw 90 q10 ∷
   rw⁻ 89 q1 ∷
   re 90 3 (ℓ "丽") ∷
   rw 90 q11 ∷
   rw 89 q9 ∷
   re 91 1 (ℓ "乏丶乏") ∷
   rw 90 q1 ∷
   rw 91 q12 ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "中") ∷
   rw 91 q2 ∷
   rw 86 q17 ∷
   rw 87 q8 ∷
   rw⁻ 86 q9 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q1 ∷
   rw 86 q10 ∷
   rw⁻ 85 q1 ∷
   re 86 3 (ℓ "丽") ∷
   rw 86 q11 ∷
   rw 85 q9 ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q1 ∷
   rw 87 q12 ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   rw 87 q2 ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q3 ∷
   re 90 3 (ℓ "乓") ∷
   rw 89 q4 ∷
   rw 88 q5 ∷
   rw 87 q6 ∷
   re 87 1 (ℓ "乏乆乏") ∷
   rw 86 q7 ∷
   re 87 5 (ℓ "中") ∷
   rw 89 q8 ∷
   rw⁻ 88 q9 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw⁻ 89 q1 ∷
   rw 88 q10 ∷
   rw⁻ 87 q1 ∷
   re 88 3 (ℓ "丽") ∷
   rw 88 q11 ∷
   rw 87 q9 ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q1 ∷
   rw 89 q12 ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "中") ∷
   rw 89 q2 ∷
   rw 86 q8 ∷
   rw⁻ 85 q9 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw⁻ 86 q1 ∷
   rw 85 q10 ∷
   rw⁻ 84 q1 ∷
   re 85 3 (ℓ "丽") ∷
   rw 85 q11 ∷
   rw 84 q9 ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q1 ∷
   rw 86 q12 ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q2 ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q3 ∷
   re 89 3 (ℓ "乓") ∷
   rw 88 q4 ∷
   rw 87 q5 ∷
   rw 86 q6 ∷
   re 86 1 (ℓ "乏乆乏") ∷
   rw 85 q7 ∷
   re 86 5 (ℓ "中") ∷
   rw 88 q8 ∷
   rw⁻ 87 q9 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw⁻ 88 q1 ∷
   rw 87 q10 ∷
   rw⁻ 86 q1 ∷
   re 87 3 (ℓ "丽") ∷
   rw 87 q11 ∷
   rw 86 q9 ∷
   re 88 1 (ℓ "乏丶乏") ∷
   rw 87 q1 ∷
   rw 88 q12 ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "中") ∷
   rw 88 q2 ∷
   rw 85 q8 ∷
   rw⁻ 84 q9 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q1 ∷
   rw 84 q10 ∷
   rw⁻ 83 q1 ∷
   re 84 3 (ℓ "丽") ∷
   rw 84 q11 ∷
   rw 83 q9 ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q1 ∷
   rw 85 q12 ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   rw 85 q2 ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q3 ∷
   re 88 3 (ℓ "乓") ∷
   rw 87 q4 ∷
   rw 86 q5 ∷
   rw 85 q6 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q7 ∷
   re 85 5 (ℓ "中") ∷
   rw 87 q8 ∷
   rw⁻ 86 q9 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q1 ∷
   rw 86 q10 ∷
   rw⁻ 85 q1 ∷
   re 86 3 (ℓ "丽") ∷
   rw 86 q11 ∷
   rw 85 q9 ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q1 ∷
   rw 87 q12 ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   rw 87 q2 ∷
   rw 84 q8 ∷
   rw⁻ 83 q9 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q1 ∷
   rw 83 q10 ∷
   rw⁻ 82 q1 ∷
   re 83 3 (ℓ "丽") ∷
   rw 83 q11 ∷
   rw 82 q9 ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q1 ∷
   rw 84 q12 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q2 ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q3 ∷
   re 87 3 (ℓ "乓") ∷
   rw 86 q4 ∷
   rw 85 q5 ∷
   rw 84 q6 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q7 ∷
   re 84 5 (ℓ "中") ∷
   rw 86 q8 ∷
   rw⁻ 85 q9 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw⁻ 86 q1 ∷
   rw 85 q10 ∷
   rw⁻ 84 q1 ∷
   re 85 3 (ℓ "丽") ∷
   rw 85 q11 ∷
   rw 84 q9 ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q1 ∷
   rw 86 q12 ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q2 ∷
   rw 83 q8 ∷
   rw⁻ 82 q9 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q1 ∷
   rw 82 q10 ∷
   rw⁻ 81 q1 ∷
   re 82 3 (ℓ "丽") ∷
   rw 82 q11 ∷
   rw 81 q9 ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q1 ∷
   rw 83 q12 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   rw 83 q2 ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q3 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q4 ∷
   rw 84 q5 ∷
   rw 83 q6 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q7 ∷
   re 83 5 (ℓ "中") ∷
   rw 85 q8 ∷
   rw⁻ 84 q9 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q1 ∷
   rw 84 q10 ∷
   rw⁻ 83 q1 ∷
   re 84 3 (ℓ "丽") ∷
   rw 84 q11 ∷
   rw 83 q9 ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q1 ∷
   rw 85 q12 ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   rw 85 q2 ∷
   rw 82 q8 ∷
   rw⁻ 81 q9 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q1 ∷
   rw 81 q10 ∷
   rw⁻ 80 q1 ∷
   re 81 3 (ℓ "丽") ∷
   rw 81 q11 ∷
   rw 80 q9 ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q1 ∷
   rw 82 q12 ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   rw 82 q2 ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q3 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q4 ∷
   rw 83 q5 ∷
   rw 82 q6 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q7 ∷
   re 82 5 (ℓ "中") ∷
   rw 84 q8 ∷
   rw⁻ 83 q9 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q1 ∷
   rw 83 q10 ∷
   rw⁻ 82 q1 ∷
   re 83 3 (ℓ "丽") ∷
   rw 83 q11 ∷
   rw 82 q9 ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q1 ∷
   rw 84 q12 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q2 ∷
   rw 81 q8 ∷
   rw⁻ 80 q9 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q1 ∷
   rw 80 q10 ∷
   rw⁻ 79 q1 ∷
   re 80 3 (ℓ "丽") ∷
   rw 80 q11 ∷
   rw 79 q9 ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q1 ∷
   rw 81 q12 ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   rw 81 q2 ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q3 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q4 ∷
   rw 82 q5 ∷
   rw 81 q6 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q7 ∷
   re 81 5 (ℓ "中") ∷
   rw 83 q8 ∷
   rw⁻ 82 q9 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q1 ∷
   rw 82 q10 ∷
   rw⁻ 81 q1 ∷
   re 82 3 (ℓ "丽") ∷
   rw 82 q11 ∷
   rw 81 q9 ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q1 ∷
   rw 83 q12 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   rw 83 q2 ∷
   rw 80 q8 ∷
   rw⁻ 79 q9 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q1 ∷ []) Eq.refl
