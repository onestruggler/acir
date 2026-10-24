{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D062 (W : Ws) where

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
  q2 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 113 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q6 : Eqn
  q6 = wE 114 W
  q7 : Eqn
  q7 = wE 486 W
  q8 : Eqn
  q8 = wE 173 W
  q9 : Eqn
  q9 = wE 557 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = wE 566 W
  q12 : Eqn
  q12 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q13 : Eqn
  q13 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q14 : Eqn
  q14 = wE 567 W
  q15 : Eqn
  q15 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q19 : Eqn
  q19 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q20 : Eqn
  q20 = wE 487 W

-- Bar(SSSKSS;3,2->0) passes groups of WBar(SSKSKK;~3,1->0) part1: 500 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part1 : ⟪ (ℓ "丞中中乑中乑乑丞中中中乑中中乖丧丧丧丞乏乆中乏丞丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠中中中乑中中乖丧丧丧丞乏乏乓丼丠丼乏乏丞丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part1 = derive (ℓ "丞中中乑中乑乑丞中中中乑中中乖丧丧丧丞乏乆中乏丞丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧临与临与丠丠丠临与丠丠丠丠丠丠丞乓丞丠丠临丠临临") (ℓ "丞中中乑中乑乑丞丞乓丞临与临与丠丠丠临与丠丠丠丠丠丠中中中乑中中乖丧丧丧丞乏乏乓丼丠丼乏乏丞丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丠丠临丠临临")
  (re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q1 ∷
   re 19 3 (ℓ "乓") ∷
   rw 20 q2 ∷
   rw 17 q2 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q3 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q1 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q1 ∷
   re 18 3 (ℓ "乓") ∷
   rw 19 q2 ∷
   rw 16 q2 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q3 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q1 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q1 ∷
   re 17 3 (ℓ "乓") ∷
   rw 18 q2 ∷
   rw 15 q2 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q3 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q1 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q1 ∷
   re 16 3 (ℓ "乓") ∷
   rw 17 q2 ∷
   rw 14 q7 ∷
   rw 17 q3 ∷
   rw 16 q8 ∷
   re 15 1 (ℓ "乏乆乏") ∷
   rw 17 q1 ∷
   rw 14 q8 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q1 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q1 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q1 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q1 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q1 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q1 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "乓") ∷
   rw 10 q10 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "乑") ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q1 ∷
   rw 36 q11 ∷
   rw⁻ 35 q12 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 38 q13 ∷
   rw⁻ 39 q5 ∷
   rw⁻ 40 q5 ∷
   rw⁻ 41 q5 ∷
   rw⁻ 42 q12 ∷
   rw⁻ 43 q13 ∷
   rw⁻ 44 q5 ∷
   rw⁻ 45 q5 ∷
   rw⁻ 46 q5 ∷
   rw⁻ 47 q5 ∷
   rw⁻ 48 q5 ∷
   rw⁻ 49 q5 ∷
   rw 18 q14 ∷
   rw⁻ 17 q12 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 19 q12 ∷
   rw⁻ 20 q13 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q12 ∷
   rw⁻ 25 q13 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 31 q5 ∷
   rw 32 q3 ∷
   rw 31 q15 ∷
   rw 30 q15 ∷
   rw 29 q15 ∷
   rw 28 q15 ∷
   rw 27 q15 ∷
   rw 26 q15 ∷
   rw 25 q16 ∷
   rw 24 q17 ∷
   rw 23 q15 ∷
   rw 22 q15 ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   rw 19 q17 ∷
   rw 18 q16 ∷
   rw 17 q17 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q1 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q1 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q1 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q1 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q1 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q1 ∷
   rw 12 q11 ∷
   rw⁻ 11 q17 ∷
   rw⁻ 12 q16 ∷
   rw⁻ 13 q17 ∷
   rw⁻ 14 q16 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 18 q17 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 22 q15 ∷
   rw⁻ 23 q15 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 25 q15 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "乑") ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q1 ∷
   rw 56 q2 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q3 ∷
   re 58 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q3 ∷
   re 62 3 (ℓ "乓") ∷
   rw 61 q4 ∷
   rw 60 q5 ∷
   rw 59 q6 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q1 ∷
   re 59 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q1 ∷
   re 57 3 (ℓ "乓") ∷
   rw 58 q2 ∷
   rw 55 q2 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q3 ∷
   re 57 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q3 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q4 ∷
   rw 59 q5 ∷
   rw 58 q6 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q1 ∷
   re 58 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q1 ∷
   re 56 3 (ℓ "乓") ∷
   rw 57 q2 ∷
   rw 54 q18 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q3 ∷
   re 56 3 (ℓ "乑") ∷
   re 56 1 (ℓ "乏丼临丼乏") ∷
   rw 62 q3 ∷
   re 60 3 (ℓ "乓") ∷
   rw 59 q4 ∷
   rw 58 q12 ∷
   rw 57 q6 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q1 ∷
   re 57 5 (ℓ "乑") ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 59 q1 ∷
   re 55 3 (ℓ "乓") ∷
   rw 56 q18 ∷
   rw 53 q2 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q3 ∷
   re 55 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q3 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q4 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q1 ∷
   re 56 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q2 ∷
   rw 52 q2 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q3 ∷
   re 54 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q3 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q4 ∷
   rw 56 q5 ∷
   rw 55 q6 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q1 ∷
   re 55 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q1 ∷
   re 53 3 (ℓ "乓") ∷
   rw 54 q2 ∷
   rw 51 q2 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q3 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q3 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q4 ∷
   rw 55 q5 ∷
   rw 54 q6 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q1 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q1 ∷
   re 52 3 (ℓ "乓") ∷
   rw 53 q2 ∷
   rw 50 q7 ∷
   rw 49 q2 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q3 ∷
   re 51 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   rw 52 q6 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q1 ∷
   re 52 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q1 ∷
   re 50 3 (ℓ "乓") ∷
   rw 51 q2 ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q3 ∷
   re 50 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q3 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   rw 51 q6 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q1 ∷
   re 51 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q1 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q2 ∷
   rw 47 q2 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q3 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q3 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q4 ∷
   rw 51 q5 ∷
   rw 50 q6 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q1 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q1 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q2 ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q3 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q3 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   rw 49 q6 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q1 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q1 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q2 ∷
   rw 45 q2 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q3 ∷
   re 47 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   rw 48 q6 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q1 ∷
   re 48 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q1 ∷
   re 46 3 (ℓ "乓") ∷
   rw 47 q2 ∷
   rw 44 q2 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q3 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q4 ∷
   rw 48 q5 ∷
   rw 47 q6 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q1 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q1 ∷
   re 45 3 (ℓ "乓") ∷
   rw 46 q2 ∷
   rw 43 q2 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q3 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q3 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q4 ∷
   rw 47 q5 ∷
   rw 46 q6 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q1 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q1 ∷
   re 44 3 (ℓ "乓") ∷
   rw 45 q2 ∷
   rw 42 q2 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q3 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q3 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q4 ∷
   rw 46 q5 ∷
   rw 45 q6 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q1 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q1 ∷
   re 43 3 (ℓ "乓") ∷
   rw 44 q2 ∷
   rw 41 q2 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q3 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q3 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q4 ∷
   rw 45 q5 ∷
   rw 44 q6 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q1 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q1 ∷
   re 42 3 (ℓ "乓") ∷
   rw 43 q2 ∷
   rw 40 q19 ∷
   rw 41 q20 ∷
   rw 42 q19 ∷
   rw 39 q18 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q3 ∷
   re 41 3 (ℓ "乑") ∷
   re 41 1 (ℓ "乏丼临丼乏") ∷
   rw 47 q3 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q4 ∷
   rw 43 q12 ∷
   rw 42 q6 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q1 ∷
   re 42 5 (ℓ "乑") ∷
   re 42 1 (ℓ "乏乄乏") ∷
   rw 44 q1 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q18 ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q3 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q3 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   rw 41 q6 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q1 ∷
   re 39 3 (ℓ "乓") ∷
   rw 40 q2 ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q3 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q3 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q4 ∷
   rw 41 q5 ∷
   rw 40 q6 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q1 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q1 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q2 ∷
   rw 36 q2 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q3 ∷
   re 38 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q3 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q4 ∷
   rw 40 q5 ∷
   rw 39 q6 ∷ []) Eq.refl
