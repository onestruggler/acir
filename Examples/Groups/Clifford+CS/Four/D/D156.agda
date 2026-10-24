{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D156 (W : Ws) where

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
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 629 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 31 W
  q9 : Eqn
  q9 = wE 1 W
  q10 : Eqn
  q10 = wE 113 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q12 : Eqn
  q12 = wE 114 W
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

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乏乓丼丠丼乏丘乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乏乄並乏丘並乆丘业乑业中中中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乏乓丼丠丼乏丘乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乏乄並乏丘並乆丘业乑业中中中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q1 ∷
   re 33 5 (ℓ "中") ∷
   rw 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q4 ∷
   rw 34 q5 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (ℓ "丽") ∷
   rw 34 q6 ∷
   rw 33 q3 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q4 ∷
   rw 35 q7 ∷
   rw 36 q4 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q8 ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q4 ∷
   rw 31 q5 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q6 ∷
   rw 30 q3 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q4 ∷
   rw 32 q7 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q8 ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q9 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q12 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q1 ∷
   re 32 5 (ℓ "中") ∷
   rw 34 q2 ∷
   rw⁻ 33 q3 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q4 ∷
   rw 33 q5 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q6 ∷
   rw 32 q3 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q4 ∷
   rw 34 q7 ∷
   rw 35 q4 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q8 ∷
   rw 29 q13 ∷
   rw 30 q2 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q4 ∷
   rw 29 q5 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q6 ∷
   rw 28 q3 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q4 ∷
   rw 30 q7 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q8 ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q9 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q12 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q1 ∷
   re 30 5 (ℓ "中") ∷
   rw 32 q2 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q4 ∷
   rw 31 q5 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q6 ∷
   rw 30 q3 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q4 ∷
   rw 32 q7 ∷
   rw 33 q4 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q8 ∷
   rw 29 q2 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q4 ∷
   rw 28 q5 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q6 ∷
   rw 27 q3 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q4 ∷
   rw 29 q7 ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q8 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q9 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q10 ∷
   rw 30 q11 ∷
   rw 29 q12 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q1 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q2 ∷
   rw⁻ 30 q3 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q4 ∷
   rw 30 q5 ∷
   rw⁻ 29 q4 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q6 ∷
   rw 29 q3 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q4 ∷
   rw 31 q7 ∷
   rw 32 q4 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q8 ∷
   rw 28 q2 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q6 ∷
   rw 26 q3 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q4 ∷
   rw 28 q7 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q8 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q9 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   rw 28 q12 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q1 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q2 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q4 ∷
   rw 29 q5 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q6 ∷
   rw 28 q3 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q4 ∷
   rw 30 q7 ∷
   rw 31 q4 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q8 ∷
   rw 27 q2 ∷
   rw⁻ 26 q3 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q4 ∷
   rw 26 q5 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q6 ∷
   rw 25 q3 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q4 ∷
   rw 27 q7 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q8 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q9 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   rw 27 q12 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q1 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q2 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q4 ∷
   rw 28 q5 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q6 ∷
   rw 27 q3 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q4 ∷
   rw 29 q7 ∷
   rw 30 q4 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q8 ∷
   rw 26 q2 ∷
   rw⁻ 25 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q4 ∷
   rw 25 q5 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q6 ∷
   rw 24 q3 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q4 ∷
   rw 26 q7 ∷
   rw 27 q4 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q8 ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q9 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   rw 26 q12 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q1 ∷
   re 26 5 (ℓ "中") ∷
   rw 28 q2 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q4 ∷
   rw 27 q5 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q6 ∷
   rw 26 q3 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q4 ∷
   rw 28 q7 ∷
   rw 29 q4 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q8 ∷
   rw 25 q2 ∷
   rw⁻ 24 q3 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q4 ∷
   rw 24 q5 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q6 ∷
   rw 23 q3 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q4 ∷
   rw 25 q7 ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q8 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q9 ∷
   re 28 3 (ℓ "乓") ∷
   rw 27 q10 ∷
   rw 26 q11 ∷
   rw 25 q12 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q1 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q2 ∷
   rw⁻ 26 q3 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q4 ∷
   rw 26 q5 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q6 ∷
   rw 25 q3 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q4 ∷
   rw 27 q7 ∷
   rw 28 q4 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q8 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 23 q15 ∷
   rw⁻ 24 q14 ∷
   rw 23 q2 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (ℓ "乏乄乏") ∷
   rw⁻ 23 q4 ∷
   rw 22 q16 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (ℓ "乔") ∷
   rw 22 q17 ∷
   rw 21 q3 ∷
   re 23 1 (ℓ "乏乇乏") ∷
   rw 22 q4 ∷
   rw 23 q18 ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "乑") ∷
   rw 23 q8 ∷
   re 22 1 (ℓ "乏丼临丼乏") ∷
   rw 28 q9 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q10 ∷
   rw 24 q19 ∷
   rw 23 q12 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q1 ∷
   re 23 5 (ℓ "乑") ∷
   rw 25 q2 ∷
   rw⁻ 24 q3 ∷
   re 23 1 (ℓ "乏乄乏") ∷
   rw⁻ 25 q4 ∷
   rw 24 q16 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (ℓ "乔") ∷
   rw 24 q17 ∷
   rw 23 q3 ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 24 q4 ∷
   rw 25 q18 ∷
   rw 26 q4 ∷
   re 24 3 (ℓ "乑") ∷
   rw 25 q8 ∷
   rw 22 q2 ∷
   rw⁻ 21 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q4 ∷
   rw 21 q5 ∷
   rw⁻ 20 q4 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q6 ∷
   rw 20 q3 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q4 ∷
   rw 22 q7 ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q8 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q9 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q10 ∷
   rw 23 q11 ∷
   rw 22 q12 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q1 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q2 ∷
   rw⁻ 23 q3 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q4 ∷
   rw 23 q5 ∷
   rw⁻ 22 q4 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q6 ∷
   rw 22 q3 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q4 ∷
   rw 24 q7 ∷
   rw 25 q4 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q8 ∷
   rw 21 q2 ∷
   rw⁻ 20 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q4 ∷
   rw 20 q5 ∷
   rw⁻ 19 q4 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q6 ∷
   rw 19 q3 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q4 ∷
   rw 21 q7 ∷
   rw 22 q4 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q8 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q9 ∷
   re 24 3 (ℓ "乓") ∷
   rw 23 q10 ∷
   rw 22 q11 ∷
   rw 21 q12 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q1 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q2 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q4 ∷
   rw 22 q5 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q6 ∷
   rw 21 q3 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q4 ∷
   rw 23 q7 ∷
   rw 24 q4 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q8 ∷
   rw 20 q2 ∷
   rw⁻ 19 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q4 ∷
   rw 19 q5 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q6 ∷
   rw 18 q3 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q4 ∷
   rw 20 q7 ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q8 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q9 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q10 ∷
   rw 21 q11 ∷
   rw 20 q12 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q1 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q2 ∷
   rw⁻ 21 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q4 ∷
   rw 21 q5 ∷
   rw⁻ 20 q4 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q6 ∷
   rw 20 q3 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q4 ∷
   rw 22 q7 ∷
   rw 23 q4 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q8 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 19 q14 ∷
   rw 18 q2 ∷
   rw⁻ 17 q3 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw⁻ 18 q4 ∷
   rw 17 q16 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (ℓ "乔") ∷
   rw 17 q17 ∷
   rw 16 q3 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q4 ∷
   rw 18 q18 ∷
   rw 19 q4 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q8 ∷
   re 17 1 (ℓ "乏丼临丼乏") ∷
   rw 23 q9 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q10 ∷
   rw 19 q19 ∷
   rw 18 q12 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q1 ∷
   re 18 5 (ℓ "乑") ∷
   rw 20 q2 ∷
   rw⁻ 19 q3 ∷
   re 18 1 (ℓ "乏乄乏") ∷
   rw⁻ 20 q4 ∷
   rw 19 q16 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (ℓ "乔") ∷
   rw 19 q17 ∷
   rw 18 q3 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q4 ∷
   rw 20 q18 ∷
   rw 21 q4 ∷
   re 19 3 (ℓ "乑") ∷
   rw 20 q8 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 17 q14 ∷
   rw 16 q2 ∷
   rw⁻ 15 q3 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q4 ∷ []) Eq.refl
