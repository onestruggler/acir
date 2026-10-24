{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D038 (W : Ws) where

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
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 504 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 113 W
  q15 : Eqn
  q15 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q16 : Eqn
  q16 = wE 114 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q19 : Eqn
  q19 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q20 : Eqn
  q20 = wE 486 W
  q21 : Eqn
  q21 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q22 : Eqn
  q22 = wE 487 W
  q23 : Eqn
  q23 = wE 173 W

-- Bar(SSKSKK;3,2->0) passes groups of WBar(SSKSKK;~3,1->0) part0: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part0 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑丞中中乑乏丧乏乏乄乄丘乆丘乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part0 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临") (ℓ "丞中中乑中乑乑丞中中乑乏丧乏乏乄乄丘乆丘乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临")
  (rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q3 ∷
   rw 35 q4 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q3 ∷
   rw 34 q5 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "乔") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q5 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q5 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw⁻ 22 q6 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw⁻ 15 q7 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw⁻ 10 q7 ∷
   rw 9 q4 ∷
   rw⁻ 8 q7 ∷
   rw 7 q4 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q5 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw 3 q9 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q3 ∷
   rw 4 q10 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "乑") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q3 ∷
   rw 6 q10 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q3 ∷
   rw 7 q10 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q3 ∷
   rw 10 q9 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q3 ∷
   rw 11 q10 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q3 ∷
   rw 13 q10 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q3 ∷
   rw 14 q10 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q6 ∷
   rw 15 q10 ∷
   rw 16 q7 ∷
   rw 17 q10 ∷
   rw 18 q7 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q10 ∷
   rw 23 q7 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   rw 31 q9 ∷
   rw 32 q9 ∷
   rw 33 q10 ∷
   rw 34 q9 ∷
   rw 35 q10 ∷
   rw 36 q10 ∷
   rw 37 q11 ∷
   rw 36 q12 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q13 ∷
   re 38 3 (ℓ "乑") ∷
   re 38 1 (ℓ "乏丼临丼乏") ∷
   rw 44 q13 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q14 ∷
   rw 40 q15 ∷
   rw 39 q16 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q17 ∷
   re 39 5 (ℓ "乑") ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw 41 q17 ∷
   re 37 3 (ℓ "乓") ∷
   rw 38 q12 ∷
   rw 35 q12 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q13 ∷
   re 37 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏丼临丼乏") ∷
   rw 43 q13 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q14 ∷
   rw 39 q15 ∷
   rw 38 q16 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q17 ∷
   re 38 5 (ℓ "乑") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q17 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q12 ∷
   rw 34 q18 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q13 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q13 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q14 ∷
   rw 38 q19 ∷
   rw 37 q16 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q17 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q17 ∷
   re 35 3 (ℓ "乓") ∷
   rw 36 q18 ∷
   rw 33 q12 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q13 ∷
   re 35 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏丼临丼乏") ∷
   rw 41 q13 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q14 ∷
   rw 37 q15 ∷
   rw 36 q16 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q17 ∷
   re 36 5 (ℓ "乑") ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q17 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q12 ∷
   rw 32 q18 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q13 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q13 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q14 ∷
   rw 36 q19 ∷
   rw 35 q16 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q17 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q17 ∷
   re 33 3 (ℓ "乓") ∷
   rw 34 q18 ∷
   rw 31 q18 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q13 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q13 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q14 ∷
   rw 35 q19 ∷
   rw 34 q16 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q17 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q17 ∷
   re 32 3 (ℓ "乓") ∷
   rw 33 q18 ∷
   rw 30 q20 ∷
   rw 29 q18 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q13 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q13 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q14 ∷
   rw 33 q19 ∷
   rw 32 q16 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q17 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q17 ∷
   re 30 3 (ℓ "乓") ∷
   rw 31 q18 ∷
   rw 28 q18 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q13 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q13 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q14 ∷
   rw 32 q19 ∷
   rw 31 q16 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q17 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q17 ∷
   re 29 3 (ℓ "乓") ∷
   rw 30 q18 ∷
   rw 27 q18 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q13 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q13 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q14 ∷
   rw 31 q19 ∷
   rw 30 q16 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q17 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q17 ∷
   re 28 3 (ℓ "乓") ∷
   rw 29 q18 ∷
   rw 26 q18 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q13 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q13 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q14 ∷
   rw 30 q19 ∷
   rw 29 q16 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q17 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q17 ∷
   re 27 3 (ℓ "乓") ∷
   rw 28 q18 ∷
   rw 25 q18 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q13 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q13 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q14 ∷
   rw 29 q19 ∷
   rw 28 q16 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q17 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q17 ∷
   re 26 3 (ℓ "乓") ∷
   rw 27 q18 ∷
   rw 24 q18 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q13 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q13 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q14 ∷
   rw 28 q19 ∷
   rw 27 q16 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q17 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q17 ∷
   re 25 3 (ℓ "乓") ∷
   rw 26 q18 ∷
   rw 23 q21 ∷
   rw 24 q22 ∷
   rw 25 q21 ∷
   rw 22 q12 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q13 ∷
   re 24 3 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼临丼乏") ∷
   rw 30 q13 ∷
   re 28 3 (ℓ "乓") ∷
   rw 27 q14 ∷
   rw 26 q15 ∷
   rw 25 q16 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q17 ∷
   re 25 5 (ℓ "乑") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q17 ∷
   re 23 3 (ℓ "乓") ∷
   rw 24 q12 ∷
   rw 21 q18 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q13 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q13 ∷
   re 27 3 (ℓ "乓") ∷
   rw 26 q14 ∷
   rw 25 q19 ∷
   rw 24 q16 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q17 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q17 ∷
   re 22 3 (ℓ "乓") ∷
   rw 23 q18 ∷
   rw 20 q18 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q13 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q13 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q14 ∷
   rw 24 q19 ∷
   rw 23 q16 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q17 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q17 ∷
   re 21 3 (ℓ "乓") ∷
   rw 22 q18 ∷
   rw 19 q18 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q13 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q13 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q14 ∷
   rw 23 q19 ∷
   rw 22 q16 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q17 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q17 ∷
   re 20 3 (ℓ "乓") ∷
   rw 21 q18 ∷
   rw 18 q21 ∷
   rw 19 q22 ∷
   rw 20 q21 ∷
   rw 17 q12 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q13 ∷
   re 19 3 (ℓ "乑") ∷
   re 19 1 (ℓ "乏丼临丼乏") ∷
   rw 25 q13 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q14 ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q17 ∷
   re 20 5 (ℓ "乑") ∷
   re 20 1 (ℓ "乏乄乏") ∷
   rw 22 q17 ∷
   re 18 3 (ℓ "乓") ∷
   rw 19 q12 ∷
   rw 16 q21 ∷
   rw 17 q22 ∷
   rw 18 q21 ∷
   rw 15 q12 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q13 ∷
   re 17 3 (ℓ "乑") ∷
   re 17 1 (ℓ "乏丼临丼乏") ∷
   rw 23 q13 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q14 ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q17 ∷
   re 18 5 (ℓ "乑") ∷
   re 18 1 (ℓ "乏乄乏") ∷
   rw 20 q17 ∷
   re 16 3 (ℓ "乓") ∷
   rw 17 q12 ∷
   rw 14 q20 ∷
   rw 17 q13 ∷
   rw 16 q23 ∷
   re 15 1 (ℓ "乏乆乏") ∷
   rw 17 q17 ∷
   rw 14 q23 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q17 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q17 ∷
   re 11 1 (ℓ "乏丧乏") ∷ []) Eq.refl
