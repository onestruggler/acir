{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D124 (W : Ws) where

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
  q2 = wE 629 W
  q3 : Eqn
  q3 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
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
  q21 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q23 : Eqn
  q23 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q24 : Eqn
  q24 = wE 678 W
  q25 : Eqn
  q25 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))

-- Bar(SSKSKK;2,3->0) passes groups of WBar(SSSKSS;~2,1->0) part1: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part1 : ⟪ (ℓ "丘丧丧丧乄丧丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中乏並丶乏丘並乆丘中乌中中乑中乑乑丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丘乆丘丠丠丠临丠丠") ⟫ʷ ≈ ⟪ (ℓ "丘丧丧丧乄丧丧丘丘乆丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中丠丠丠丠乌丠丠临与丠丠丠丠丠丠丠丠丠中中乑中乑乑丘乆丘丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part1 = derive (ℓ "丘丧丧丧乄丧丧丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中乏並丶乏丘並乆丘中乌中中乑中乑乑丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠丘乆丘丠丠丠临丠丠") (ℓ "丘丧丧丧乄丧丧丘丘乆丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中丠丠丠丠乌丠丠临与丠丠丠丠丠丠丠丠丠中中乑中乑乑丘乆丘丠丠丠临丠丠")
  (rw⁻ 28 q1 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q1 ∷
   rw 30 q4 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q6 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q7 ∷
   rw 31 q8 ∷
   rw 30 q9 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q10 ∷
   re 30 5 (ℓ "中") ∷
   rw 32 q11 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q1 ∷
   rw 31 q12 ∷
   rw⁻ 30 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q1 ∷
   rw 32 q4 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q5 ∷
   rw 29 q11 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q1 ∷
   rw 28 q12 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q1 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q5 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q6 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q7 ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q10 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q11 ∷
   rw⁻ 30 q3 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q1 ∷
   rw 30 q12 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q1 ∷
   rw 31 q4 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q5 ∷
   rw 28 q11 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q1 ∷
   rw 27 q12 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q1 ∷
   rw 28 q4 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q5 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q6 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   rw 28 q9 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q10 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q11 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q1 ∷
   rw 29 q12 ∷
   rw⁻ 28 q1 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q1 ∷
   rw 30 q4 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   rw 27 q11 ∷
   rw⁻ 26 q3 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q1 ∷
   rw 26 q12 ∷
   rw⁻ 25 q1 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q1 ∷
   rw 27 q4 ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q5 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q6 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q7 ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q10 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q11 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q1 ∷
   rw 28 q12 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q1 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q5 ∷
   rw 26 q11 ∷
   rw⁻ 25 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q1 ∷
   rw 25 q12 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q1 ∷
   rw 26 q4 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q5 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q6 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q7 ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q10 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q11 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q1 ∷
   rw 27 q12 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q1 ∷
   rw 28 q4 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q5 ∷
   rw⁻ 23 q13 ∷
   rw⁻ 24 q14 ∷
   rw⁻ 25 q13 ∷
   rw 24 q11 ∷
   rw⁻ 23 q3 ∷
   re 22 1 (ℓ "乏乄乏") ∷
   rw⁻ 24 q1 ∷
   rw 23 q15 ∷
   rw⁻ 22 q1 ∷
   re 23 3 (ℓ "乔") ∷
   rw 23 q16 ∷
   rw 22 q3 ∷
   re 24 1 (ℓ "乏乇乏") ∷
   rw 23 q1 ∷
   rw 24 q17 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乑") ∷
   rw 24 q5 ∷
   re 23 1 (ℓ "乏丼临丼乏") ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "乓") ∷
   rw 26 q7 ∷
   rw 25 q18 ∷
   rw 24 q9 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q10 ∷
   re 24 5 (ℓ "乑") ∷
   rw 26 q11 ∷
   rw⁻ 25 q3 ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw⁻ 26 q1 ∷
   rw 25 q15 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (ℓ "乔") ∷
   rw 25 q16 ∷
   rw 24 q3 ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q1 ∷
   rw 26 q17 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乑") ∷
   rw 26 q5 ∷
   rw 23 q11 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q1 ∷
   rw 22 q12 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q1 ∷
   rw 23 q4 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q5 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q7 ∷
   rw 24 q8 ∷
   rw 23 q9 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q10 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q11 ∷
   rw⁻ 24 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q1 ∷
   rw 24 q12 ∷
   rw⁻ 23 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q1 ∷
   rw 25 q4 ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q5 ∷
   rw 22 q11 ∷
   rw⁻ 21 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q1 ∷
   rw 21 q12 ∷
   rw⁻ 20 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q1 ∷
   rw 22 q4 ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q5 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q7 ∷
   rw 23 q8 ∷
   rw 22 q9 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q10 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q11 ∷
   rw⁻ 23 q3 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q1 ∷
   rw 23 q12 ∷
   rw⁻ 22 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q1 ∷
   rw 24 q4 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q5 ∷
   rw 21 q11 ∷
   rw⁻ 20 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q1 ∷
   rw 20 q12 ∷
   rw⁻ 19 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q1 ∷
   rw 21 q4 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q5 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "乓") ∷
   rw 23 q7 ∷
   rw 22 q8 ∷
   rw 21 q9 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q10 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q11 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q1 ∷
   rw 22 q12 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q1 ∷
   rw 23 q4 ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q5 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 20 q13 ∷
   rw 19 q11 ∷
   rw⁻ 18 q3 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw⁻ 19 q1 ∷
   rw 18 q15 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (ℓ "乔") ∷
   rw 18 q16 ∷
   rw 17 q3 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q1 ∷
   rw 19 q17 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乑") ∷
   rw 19 q5 ∷
   re 18 1 (ℓ "乏丼临丼乏") ∷
   rw 24 q6 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q7 ∷
   rw 20 q18 ∷
   rw 19 q9 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q10 ∷
   re 19 5 (ℓ "乑") ∷
   rw 21 q11 ∷
   rw⁻ 20 q3 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw⁻ 21 q1 ∷
   rw 20 q15 ∷
   rw⁻ 19 q1 ∷
   re 20 3 (ℓ "乔") ∷
   rw 20 q16 ∷
   rw 19 q3 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q1 ∷
   rw 21 q17 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q5 ∷
   rw⁻ 16 q13 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 18 q13 ∷
   rw 17 q11 ∷
   rw⁻ 16 q3 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q1 ∷
   rw 16 q15 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (ℓ "乔") ∷
   rw 16 q16 ∷
   rw 15 q3 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q1 ∷
   rw 17 q17 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q5 ∷
   re 16 1 (ℓ "乏丼临丼乏") ∷
   rw 22 q6 ∷
   re 20 3 (ℓ "乓") ∷
   rw 19 q7 ∷
   rw 18 q18 ∷
   rw 17 q9 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q10 ∷
   re 17 5 (ℓ "乑") ∷
   rw 19 q11 ∷
   rw⁻ 18 q3 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw⁻ 19 q1 ∷
   rw 18 q15 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (ℓ "乔") ∷
   rw 18 q16 ∷
   rw 17 q3 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q1 ∷
   rw 19 q17 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乑") ∷
   rw 19 q5 ∷
   rw 14 q19 ∷
   rw 8 q20 ∷
   rw 57 q6 ∷
   rw 56 q21 ∷
   rw 55 q21 ∷
   rw 54 q21 ∷
   rw 53 q21 ∷
   rw 52 q21 ∷
   rw 51 q21 ∷
   rw 50 q21 ∷
   rw 49 q21 ∷
   rw 48 q21 ∷
   rw 47 q22 ∷
   rw 46 q23 ∷
   rw 45 q21 ∷
   rw 44 q21 ∷
   rw 43 q21 ∷
   rw 42 q21 ∷
   rw 41 q21 ∷
   rw 40 q21 ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw 41 q10 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q10 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q10 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q10 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q10 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q10 ∷
   rw 35 q24 ∷
   rw⁻ 34 q21 ∷
   rw⁻ 35 q21 ∷
   rw⁻ 36 q21 ∷
   rw⁻ 37 q21 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 39 q21 ∷
   rw⁻ 40 q23 ∷
   rw⁻ 41 q22 ∷
   rw⁻ 42 q21 ∷
   rw⁻ 43 q21 ∷
   rw⁻ 44 q21 ∷
   rw⁻ 45 q21 ∷
   rw⁻ 46 q21 ∷
   rw⁻ 47 q21 ∷
   rw⁻ 48 q21 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q21 ∷
   rw 53 q6 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q6 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q6 ∷
   re 53 3 (ℓ "乑") ∷
   rw 56 q6 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q6 ∷
   re 55 3 (ℓ "乑") ∷
   rw 58 q6 ∷
   re 56 3 (ℓ "乑") ∷
   rw 57 q10 ∷
   rw⁻ 33 q25 ∷
   rw⁻ 34 q25 ∷
   rw⁻ 35 q25 ∷
   rw⁻ 36 q25 ∷ []) Eq.refl
