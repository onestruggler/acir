{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D039 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 488 W
  q3 : Eqn
  q3 = wE 175 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 505 W
  q6 : Eqn
  q6 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q8 : Eqn
  q8 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q9 : Eqn
  q9 = wE 506 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q12 : Eqn
  q12 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q13 : Eqn
  q13 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q14 : Eqn
  q14 = wE 113 W
  q15 : Eqn
  q15 = wE 114 W
  q16 : Eqn
  q16 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q17 : Eqn
  q17 = wE 486 W
  q18 : Eqn
  q18 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q19 : Eqn
  q19 = wE 487 W
  q20 : Eqn
  q20 = wE 173 W
  q21 : Eqn
  q21 = wE 507 W
  q22 : Eqn
  q22 = wE 508 W

-- Bar(SSKSKK;3,2->0) passes groups of WBar(SSKSKK;~3,1->0) part1: 500 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part1 : ⟪ (ℓ "丞中中乑中乑乑丞中中乑乏丧乏乏乄乄丘乆丘乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞乏丠丠临丠临临丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part1 = derive (ℓ "丞中中乑中乑乑丞中中乑乏丧乏乏乄乄丘乆丘乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临") (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞乏丠丠临丠临临丧丧乄丧乄乄乏乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 13 q1 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q1 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q1 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q1 ∷
   rw 9 q2 ∷
   rw 8 q3 ∷
   rw 11 q4 ∷
   re 9 3 (ℓ "乓") ∷
   rw 10 q3 ∷
   rw 13 q4 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q4 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q4 ∷
   re 13 3 (ℓ "乑") ∷
   rw 16 q4 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q4 ∷
   re 15 3 (ℓ "乑") ∷
   rw 18 q4 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q1 ∷
   rw 34 q5 ∷
   rw⁻ 33 q6 ∷
   rw⁻ 34 q7 ∷
   rw⁻ 35 q6 ∷
   rw⁻ 36 q7 ∷
   rw⁻ 37 q8 ∷
   rw⁻ 38 q8 ∷
   rw⁻ 39 q8 ∷
   rw⁻ 40 q6 ∷
   rw⁻ 41 q7 ∷
   rw⁻ 42 q8 ∷
   rw⁻ 43 q8 ∷
   rw⁻ 44 q8 ∷
   rw⁻ 45 q8 ∷
   rw⁻ 46 q8 ∷
   rw⁻ 47 q8 ∷
   rw 18 q9 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 21 q8 ∷
   rw⁻ 22 q8 ∷
   rw⁻ 23 q8 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 25 q7 ∷
   rw⁻ 26 q8 ∷
   rw⁻ 27 q8 ∷
   rw⁻ 28 q8 ∷
   rw⁻ 29 q8 ∷
   rw⁻ 30 q8 ∷
   rw⁻ 31 q8 ∷
   rw 32 q4 ∷
   rw 31 q10 ∷
   rw 30 q10 ∷
   rw 29 q10 ∷
   rw 28 q10 ∷
   rw 27 q10 ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   rw 24 q12 ∷
   rw 23 q10 ∷
   rw 22 q10 ∷
   rw 21 q10 ∷
   rw 20 q11 ∷
   rw 19 q12 ∷
   rw 18 q11 ∷
   rw 17 q12 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q1 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q1 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q1 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q1 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q1 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q1 ∷
   rw 12 q5 ∷
   rw⁻ 11 q12 ∷
   rw⁻ 12 q11 ∷
   rw⁻ 13 q12 ∷
   rw⁻ 14 q11 ∷
   rw⁻ 15 q10 ∷
   rw⁻ 16 q10 ∷
   rw⁻ 17 q10 ∷
   rw⁻ 18 q12 ∷
   rw⁻ 19 q11 ∷
   rw⁻ 20 q10 ∷
   rw⁻ 21 q10 ∷
   rw⁻ 22 q10 ∷
   rw⁻ 23 q10 ∷
   rw⁻ 24 q10 ∷
   rw⁻ 25 q10 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q1 ∷
   rw 54 q13 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q4 ∷
   re 56 3 (ℓ "乑") ∷
   re 56 1 (ℓ "乏丼临丼乏") ∷
   rw 62 q4 ∷
   re 60 3 (ℓ "乓") ∷
   rw 59 q14 ∷
   rw 58 q6 ∷
   rw 57 q15 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q1 ∷
   re 57 5 (ℓ "乑") ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 59 q1 ∷
   re 55 3 (ℓ "乓") ∷
   rw 56 q13 ∷
   rw 53 q13 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q4 ∷
   re 55 3 (ℓ "乑") ∷
   re 55 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q4 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q14 ∷
   rw 57 q6 ∷
   rw 56 q15 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q1 ∷
   re 56 5 (ℓ "乑") ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q13 ∷
   rw 52 q16 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q4 ∷
   re 54 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q4 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q14 ∷
   rw 56 q8 ∷
   rw 55 q15 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q1 ∷
   re 55 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q1 ∷
   re 53 3 (ℓ "乓") ∷
   rw 54 q16 ∷
   rw 51 q13 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q4 ∷
   re 53 3 (ℓ "乑") ∷
   re 53 1 (ℓ "乏丼临丼乏") ∷
   rw 59 q4 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q14 ∷
   rw 55 q6 ∷
   rw 54 q15 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q1 ∷
   re 54 5 (ℓ "乑") ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw 56 q1 ∷
   re 52 3 (ℓ "乓") ∷
   rw 53 q13 ∷
   rw 50 q16 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q4 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q4 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q14 ∷
   rw 54 q8 ∷
   rw 53 q15 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q1 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q1 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q16 ∷
   rw 49 q16 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q4 ∷
   re 51 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q4 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q14 ∷
   rw 53 q8 ∷
   rw 52 q15 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q1 ∷
   re 52 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q1 ∷
   re 50 3 (ℓ "乓") ∷
   rw 51 q16 ∷
   rw 48 q17 ∷
   rw 47 q16 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q4 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q4 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q14 ∷
   rw 51 q8 ∷
   rw 50 q15 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q1 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q1 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q16 ∷
   rw 46 q16 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q4 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q4 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q14 ∷
   rw 50 q8 ∷
   rw 49 q15 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q1 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q1 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q16 ∷
   rw 45 q16 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q4 ∷
   re 47 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q4 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q14 ∷
   rw 49 q8 ∷
   rw 48 q15 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q1 ∷
   re 48 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q1 ∷
   re 46 3 (ℓ "乓") ∷
   rw 47 q16 ∷
   rw 44 q16 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q4 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q4 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q14 ∷
   rw 48 q8 ∷
   rw 47 q15 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q1 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q1 ∷
   re 45 3 (ℓ "乓") ∷
   rw 46 q16 ∷
   rw 43 q16 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q4 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q4 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q14 ∷
   rw 47 q8 ∷
   rw 46 q15 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q1 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q1 ∷
   re 44 3 (ℓ "乓") ∷
   rw 45 q16 ∷
   rw 42 q16 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q4 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q4 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q14 ∷
   rw 46 q8 ∷
   rw 45 q15 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q1 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q1 ∷
   re 43 3 (ℓ "乓") ∷
   rw 44 q16 ∷
   rw 41 q18 ∷
   rw 42 q19 ∷
   rw 43 q18 ∷
   rw 40 q13 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q4 ∷
   re 42 3 (ℓ "乑") ∷
   re 42 1 (ℓ "乏丼临丼乏") ∷
   rw 48 q4 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q14 ∷
   rw 44 q6 ∷
   rw 43 q15 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q1 ∷
   re 43 5 (ℓ "乑") ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw 45 q1 ∷
   re 41 3 (ℓ "乓") ∷
   rw 42 q13 ∷
   rw 39 q16 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q4 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q4 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q14 ∷
   rw 43 q8 ∷
   rw 42 q15 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q1 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q1 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q16 ∷
   rw 38 q16 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q4 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q4 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q14 ∷
   rw 42 q8 ∷
   rw 41 q15 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q1 ∷
   re 39 3 (ℓ "乓") ∷
   rw 40 q16 ∷
   rw 37 q16 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q4 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q4 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q14 ∷
   rw 41 q8 ∷
   rw 40 q15 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q1 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q1 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q16 ∷
   rw 36 q18 ∷
   rw 37 q19 ∷
   rw 38 q18 ∷
   rw 35 q13 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q4 ∷
   re 37 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏丼临丼乏") ∷
   rw 43 q4 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q14 ∷
   rw 39 q6 ∷
   rw 38 q15 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q1 ∷
   re 38 5 (ℓ "乑") ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q1 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q13 ∷
   rw 34 q18 ∷
   rw 35 q19 ∷
   rw 36 q18 ∷
   rw 33 q13 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q4 ∷
   re 35 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏丼临丼乏") ∷
   rw 41 q4 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q14 ∷
   rw 37 q6 ∷
   rw 36 q15 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q1 ∷
   re 36 5 (ℓ "乑") ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q1 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q13 ∷
   rw 32 q17 ∷
   rw 35 q4 ∷
   rw 34 q20 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 35 q1 ∷
   rw 32 q20 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q1 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q1 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q1 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q1 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q1 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "乓") ∷
   rw 28 q3 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "乑") ∷
   rw 34 q4 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q1 ∷
   rw 52 q21 ∷
   rw⁻ 51 q8 ∷
   rw⁻ 52 q8 ∷
   rw⁻ 53 q6 ∷
   rw⁻ 54 q8 ∷
   rw⁻ 55 q6 ∷
   rw⁻ 56 q6 ∷
   rw 36 q22 ∷
   rw⁻ 35 q8 ∷
   rw⁻ 36 q8 ∷
   rw⁻ 37 q6 ∷
   rw⁻ 38 q8 ∷
   rw⁻ 39 q6 ∷
   rw⁻ 40 q6 ∷
   rw 41 q4 ∷
   rw 40 q12 ∷
   rw 39 q12 ∷
   rw 38 q10 ∷
   rw 37 q12 ∷
   rw 36 q10 ∷
   rw 35 q10 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q1 ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw 35 q1 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q1 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q1 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q1 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q1 ∷
   rw 30 q21 ∷ []) Eq.refl
