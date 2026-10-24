{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D354 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 113 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = wE 114 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q8 : Eqn
  q8 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = wE 629 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 673 W
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

-- Bar(SSKSKK;2,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,1->0) part3: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌丘中乆丘中乑中乑乑临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧乄丧乄乄乌丘乆丘乏乄乏並並业乑业中中中乑业中中中中中中乌中中乑中乑乑临与临与丠丠丠临与丠丠丠丠丠丠") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~21-⟶0⟩-part3 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌丘中乆丘中乑中乑乑临与临与丠丠丠临与丠丠丠丠丠丠") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乆丘丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠与与与临与与与与临与丧丧乄丧乄乄乌丘乆丘乏乄乏並並业乑业中中中乑业中中中中中中乌中中乑中乑乑临与临与丠丠丠临与丠丠丠丠丠丠")
  (re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "乓") ∷
   rw 89 q2 ∷
   rw 88 q3 ∷
   rw 87 q4 ∷
   re 87 1 (ℓ "乏乆乏") ∷
   rw 86 q5 ∷
   re 87 5 (ℓ "中") ∷
   rw 89 q6 ∷
   rw⁻ 88 q7 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw⁻ 89 q8 ∷
   rw 88 q9 ∷
   rw⁻ 87 q8 ∷
   re 88 3 (ℓ "丽") ∷
   rw 88 q10 ∷
   rw 87 q7 ∷
   re 89 1 (ℓ "乏丶乏") ∷
   rw 88 q8 ∷
   rw 89 q11 ∷
   rw 90 q8 ∷
   re 88 3 (ℓ "中") ∷
   rw 89 q12 ∷
   rw 84 q13 ∷
   rw 85 q6 ∷
   rw⁻ 84 q7 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q8 ∷
   rw 84 q9 ∷
   rw⁻ 83 q8 ∷
   re 84 3 (ℓ "丽") ∷
   rw 84 q10 ∷
   rw 83 q7 ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q8 ∷
   rw 85 q11 ∷
   rw 86 q8 ∷
   re 84 3 (ℓ "中") ∷
   rw 85 q12 ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "乓") ∷
   rw 87 q2 ∷
   rw 86 q3 ∷
   rw 85 q4 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q5 ∷
   re 85 5 (ℓ "中") ∷
   rw 87 q6 ∷
   rw⁻ 86 q7 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw⁻ 87 q8 ∷
   rw 86 q9 ∷
   rw⁻ 85 q8 ∷
   re 86 3 (ℓ "丽") ∷
   rw 86 q10 ∷
   rw 85 q7 ∷
   re 87 1 (ℓ "乏丶乏") ∷
   rw 86 q8 ∷
   rw 87 q11 ∷
   rw 88 q8 ∷
   re 86 3 (ℓ "中") ∷
   rw 87 q12 ∷
   rw 84 q6 ∷
   rw⁻ 83 q7 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q8 ∷
   rw 83 q9 ∷
   rw⁻ 82 q8 ∷
   re 83 3 (ℓ "丽") ∷
   rw 83 q10 ∷
   rw 82 q7 ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q8 ∷
   rw 84 q11 ∷
   rw 85 q8 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q12 ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "乓") ∷
   rw 86 q2 ∷
   rw 85 q3 ∷
   rw 84 q4 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q5 ∷
   re 84 5 (ℓ "中") ∷
   rw 86 q6 ∷
   rw⁻ 85 q7 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw⁻ 86 q8 ∷
   rw 85 q9 ∷
   rw⁻ 84 q8 ∷
   re 85 3 (ℓ "丽") ∷
   rw 85 q10 ∷
   rw 84 q7 ∷
   re 86 1 (ℓ "乏丶乏") ∷
   rw 85 q8 ∷
   rw 86 q11 ∷
   rw 87 q8 ∷
   re 85 3 (ℓ "中") ∷
   rw 86 q12 ∷
   rw 83 q6 ∷
   rw⁻ 82 q7 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q8 ∷
   rw 82 q9 ∷
   rw⁻ 81 q8 ∷
   re 82 3 (ℓ "丽") ∷
   rw 82 q10 ∷
   rw 81 q7 ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q8 ∷
   rw 83 q11 ∷
   rw 84 q8 ∷
   re 82 3 (ℓ "中") ∷
   rw 83 q12 ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q2 ∷
   rw 84 q3 ∷
   rw 83 q4 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q5 ∷
   re 83 5 (ℓ "中") ∷
   rw 85 q6 ∷
   rw⁻ 84 q7 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw⁻ 85 q8 ∷
   rw 84 q9 ∷
   rw⁻ 83 q8 ∷
   re 84 3 (ℓ "丽") ∷
   rw 84 q10 ∷
   rw 83 q7 ∷
   re 85 1 (ℓ "乏丶乏") ∷
   rw 84 q8 ∷
   rw 85 q11 ∷
   rw 86 q8 ∷
   re 84 3 (ℓ "中") ∷
   rw 85 q12 ∷
   rw 82 q6 ∷
   rw⁻ 81 q7 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q8 ∷
   rw 81 q9 ∷
   rw⁻ 80 q8 ∷
   re 81 3 (ℓ "丽") ∷
   rw 81 q10 ∷
   rw 80 q7 ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q8 ∷
   rw 82 q11 ∷
   rw 83 q8 ∷
   re 81 3 (ℓ "中") ∷
   rw 82 q12 ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q2 ∷
   rw 83 q3 ∷
   rw 82 q4 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q5 ∷
   re 82 5 (ℓ "中") ∷
   rw 84 q6 ∷
   rw⁻ 83 q7 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw⁻ 84 q8 ∷
   rw 83 q9 ∷
   rw⁻ 82 q8 ∷
   re 83 3 (ℓ "丽") ∷
   rw 83 q10 ∷
   rw 82 q7 ∷
   re 84 1 (ℓ "乏丶乏") ∷
   rw 83 q8 ∷
   rw 84 q11 ∷
   rw 85 q8 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q12 ∷
   rw 81 q6 ∷
   rw⁻ 80 q7 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw⁻ 81 q8 ∷
   rw 80 q9 ∷
   rw⁻ 79 q8 ∷
   re 80 3 (ℓ "丽") ∷
   rw 80 q10 ∷
   rw 79 q7 ∷
   re 81 1 (ℓ "乏丶乏") ∷
   rw 80 q8 ∷
   rw 81 q11 ∷
   rw 82 q8 ∷
   re 80 3 (ℓ "中") ∷
   rw 81 q12 ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q2 ∷
   rw 82 q3 ∷
   rw 81 q4 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q5 ∷
   re 81 5 (ℓ "中") ∷
   rw 83 q6 ∷
   rw⁻ 82 q7 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw⁻ 83 q8 ∷
   rw 82 q9 ∷
   rw⁻ 81 q8 ∷
   re 82 3 (ℓ "丽") ∷
   rw 82 q10 ∷
   rw 81 q7 ∷
   re 83 1 (ℓ "乏丶乏") ∷
   rw 82 q8 ∷
   rw 83 q11 ∷
   rw 84 q8 ∷
   re 82 3 (ℓ "中") ∷
   rw 83 q12 ∷
   rw 80 q6 ∷
   rw⁻ 79 q7 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw⁻ 80 q8 ∷
   rw 79 q9 ∷
   rw⁻ 78 q8 ∷
   re 79 3 (ℓ "丽") ∷
   rw 79 q10 ∷
   rw 78 q7 ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q8 ∷
   rw 80 q11 ∷
   rw 81 q8 ∷
   re 79 3 (ℓ "中") ∷
   rw 80 q12 ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q2 ∷
   rw 81 q3 ∷
   rw 80 q4 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q5 ∷
   re 80 5 (ℓ "中") ∷
   rw 82 q6 ∷
   rw⁻ 81 q7 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw⁻ 82 q8 ∷
   rw 81 q9 ∷
   rw⁻ 80 q8 ∷
   re 81 3 (ℓ "丽") ∷
   rw 81 q10 ∷
   rw 80 q7 ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q8 ∷
   rw 82 q11 ∷
   rw 83 q8 ∷
   re 81 3 (ℓ "中") ∷
   rw 82 q12 ∷
   rw⁻ 77 q14 ∷
   rw⁻ 78 q15 ∷
   rw⁻ 79 q14 ∷
   rw 78 q6 ∷
   rw⁻ 77 q7 ∷
   re 76 1 (ℓ "乏乄乏") ∷
   rw⁻ 78 q8 ∷
   rw 77 q16 ∷
   rw⁻ 76 q8 ∷
   re 77 3 (ℓ "乔") ∷
   rw 77 q17 ∷
   rw 76 q7 ∷
   re 78 1 (ℓ "乏乇乏") ∷
   rw 77 q8 ∷
   rw 78 q18 ∷
   rw 79 q8 ∷
   re 77 3 (ℓ "乑") ∷
   rw 78 q12 ∷
   re 77 1 (ℓ "乏丼临丼乏") ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "乓") ∷
   rw 80 q2 ∷
   rw 79 q19 ∷
   rw 78 q4 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q5 ∷
   re 78 5 (ℓ "乑") ∷
   rw 80 q6 ∷
   rw⁻ 79 q7 ∷
   re 78 1 (ℓ "乏乄乏") ∷
   rw⁻ 80 q8 ∷
   rw 79 q16 ∷
   rw⁻ 78 q8 ∷
   re 79 3 (ℓ "乔") ∷
   rw 79 q17 ∷
   rw 78 q7 ∷
   re 80 1 (ℓ "乏乇乏") ∷
   rw 79 q8 ∷
   rw 80 q18 ∷
   rw 81 q8 ∷
   re 79 3 (ℓ "乑") ∷
   rw 80 q12 ∷
   rw 77 q6 ∷
   rw⁻ 76 q7 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q8 ∷
   rw 76 q9 ∷
   rw⁻ 75 q8 ∷
   re 76 3 (ℓ "丽") ∷
   rw 76 q10 ∷
   rw 75 q7 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q8 ∷
   rw 77 q11 ∷
   rw 78 q8 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q12 ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "乓") ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q5 ∷
   re 77 5 (ℓ "中") ∷
   rw 79 q6 ∷
   rw⁻ 78 q7 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw⁻ 79 q8 ∷
   rw 78 q9 ∷
   rw⁻ 77 q8 ∷
   re 78 3 (ℓ "丽") ∷
   rw 78 q10 ∷
   rw 77 q7 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q8 ∷
   rw 79 q11 ∷
   rw 80 q8 ∷
   re 78 3 (ℓ "中") ∷
   rw 79 q12 ∷
   rw 76 q6 ∷
   rw⁻ 75 q7 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw⁻ 76 q8 ∷
   rw 75 q9 ∷
   rw⁻ 74 q8 ∷
   re 75 3 (ℓ "丽") ∷
   rw 75 q10 ∷
   rw 74 q7 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q8 ∷
   rw 76 q11 ∷
   rw 77 q8 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q12 ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q2 ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q5 ∷
   re 76 5 (ℓ "中") ∷
   rw 78 q6 ∷
   rw⁻ 77 q7 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q8 ∷
   rw 77 q9 ∷
   rw⁻ 76 q8 ∷
   re 77 3 (ℓ "丽") ∷
   rw 77 q10 ∷
   rw 76 q7 ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q8 ∷
   rw 78 q11 ∷
   rw 79 q8 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q12 ∷
   rw 75 q6 ∷
   rw⁻ 74 q7 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q8 ∷
   rw 74 q9 ∷
   rw⁻ 73 q8 ∷
   re 74 3 (ℓ "丽") ∷
   rw 74 q10 ∷
   rw 73 q7 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q8 ∷
   rw 75 q11 ∷
   rw 76 q8 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q12 ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q2 ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q5 ∷
   re 75 5 (ℓ "中") ∷
   rw 77 q6 ∷
   rw⁻ 76 q7 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q8 ∷
   rw 76 q9 ∷
   rw⁻ 75 q8 ∷
   re 76 3 (ℓ "丽") ∷
   rw 76 q10 ∷
   rw 75 q7 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q8 ∷
   rw 77 q11 ∷
   rw 78 q8 ∷
   re 76 3 (ℓ "中") ∷
   rw 77 q12 ∷
   rw⁻ 72 q14 ∷
   rw⁻ 73 q15 ∷
   rw⁻ 74 q14 ∷
   rw 73 q6 ∷
   rw⁻ 72 q7 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw⁻ 73 q8 ∷
   rw 72 q16 ∷
   rw⁻ 71 q8 ∷
   re 72 3 (ℓ "乔") ∷
   rw 72 q17 ∷
   rw 71 q7 ∷
   re 73 1 (ℓ "乏乇乏") ∷
   rw 72 q8 ∷
   rw 73 q18 ∷
   rw 74 q8 ∷
   re 72 3 (ℓ "乑") ∷
   rw 73 q12 ∷
   re 72 1 (ℓ "乏丼临丼乏") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q2 ∷
   rw 74 q19 ∷
   rw 73 q4 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q5 ∷
   re 73 5 (ℓ "乑") ∷
   rw 75 q6 ∷
   rw⁻ 74 q7 ∷
   re 73 1 (ℓ "乏乄乏") ∷
   rw⁻ 75 q8 ∷
   rw 74 q16 ∷
   rw⁻ 73 q8 ∷
   re 74 3 (ℓ "乔") ∷
   rw 74 q17 ∷
   rw 73 q7 ∷
   re 75 1 (ℓ "乏乇乏") ∷
   rw 74 q8 ∷
   rw 75 q18 ∷
   rw 76 q8 ∷
   re 74 3 (ℓ "乑") ∷
   rw 75 q12 ∷
   rw⁻ 70 q14 ∷
   rw⁻ 71 q15 ∷
   rw⁻ 72 q14 ∷
   rw 71 q6 ∷
   rw⁻ 70 q7 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw⁻ 71 q8 ∷
   rw 70 q16 ∷
   rw⁻ 69 q8 ∷
   re 70 3 (ℓ "乔") ∷
   rw 70 q17 ∷
   rw 69 q7 ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q8 ∷
   rw 71 q18 ∷
   rw 72 q8 ∷
   re 70 3 (ℓ "乑") ∷
   rw 71 q12 ∷
   re 70 1 (ℓ "乏丼临丼乏") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q2 ∷
   rw 72 q19 ∷
   rw 71 q4 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q5 ∷
   re 71 5 (ℓ "乑") ∷
   rw 73 q6 ∷
   rw⁻ 72 q7 ∷
   re 71 1 (ℓ "乏乄乏") ∷
   rw⁻ 73 q8 ∷
   rw 72 q16 ∷
   rw⁻ 71 q8 ∷
   re 72 3 (ℓ "乔") ∷
   rw 72 q17 ∷
   rw 71 q7 ∷
   re 73 1 (ℓ "乏乇乏") ∷
   rw 72 q8 ∷
   rw 73 q18 ∷
   rw 74 q8 ∷ []) Eq.refl
