{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D155 (W : Ws) where

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
  q1 = wE 140 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 630 W
  q4 : Eqn
  q4 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 142 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 629 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 21 W
  q13 : Eqn
  q13 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q14 : Eqn
  q14 = wE 51 W
  q15 : Eqn
  q15 = wE 3 W
  q16 : Eqn
  q16 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q17 : Eqn
  q17 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q18 : Eqn
  q18 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 739 W
  q20 : Eqn
  q20 = wE 483 W
  q21 : Eqn
  q21 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = wE 484 W
  q24 : Eqn
  q24 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q25 : Eqn
  q25 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q26 : Eqn
  q26 = wE 464 W
  q27 : Eqn
  q27 = wE 485 W
  q28 : Eqn
  q28 = wE 151 W
  q29 : Eqn
  q29 = wE 113 W
  q30 : Eqn
  q30 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q31 : Eqn
  q31 = wE 114 W
  q32 : Eqn
  q32 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中丘丷乏乄並乏丘並业中中中中中中乌中中乑中乑乑両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乏乓丼丠丼乏丘乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中丘丷乏乄並乏丘並业中中中中中中乌中中乑中乑乑両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中丘乏乓丼丠丼乏丘乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 17 q1 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (ℓ "乔") ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q2 ∷
   rw 18 q5 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q6 ∷
   rw 15 q7 ∷
   rw⁻ 14 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q2 ∷
   rw 14 q8 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q9 ∷
   rw 13 q4 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q2 ∷
   rw 15 q10 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q6 ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q11 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q12 ∷
   rw 16 q13 ∷
   rw 15 q14 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q15 ∷
   re 15 5 (ℓ "中") ∷
   rw 17 q7 ∷
   rw⁻ 16 q4 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q2 ∷
   rw 16 q8 ∷
   rw⁻ 15 q2 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q9 ∷
   rw 15 q4 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q2 ∷
   rw 17 q10 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q6 ∷
   rw 14 q7 ∷
   rw⁻ 13 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q2 ∷
   rw 13 q8 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q9 ∷
   rw 12 q4 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   rw 14 q10 ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q6 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q11 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q12 ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q15 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q7 ∷
   rw⁻ 15 q4 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q2 ∷
   rw 15 q8 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q9 ∷
   rw 14 q4 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q2 ∷
   rw 16 q10 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q6 ∷
   rw 13 q7 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q8 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q9 ∷
   rw 11 q4 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q2 ∷
   rw 13 q10 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q6 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q11 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q12 ∷
   rw 14 q13 ∷
   rw 13 q14 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q15 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q7 ∷
   rw⁻ 14 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q2 ∷
   rw 14 q8 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q9 ∷
   rw 13 q4 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q2 ∷
   rw 15 q10 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q6 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 11 q17 ∷
   rw⁻ 12 q16 ∷
   rw 11 q7 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q3 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q2 ∷
   rw 11 q5 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丼临丼乏") ∷
   rw 16 q11 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q12 ∷
   rw 12 q18 ∷
   rw 11 q14 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q15 ∷
   re 11 5 (ℓ "乑") ∷
   rw 13 q7 ∷
   rw⁻ 12 q4 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q1 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "乔") ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q2 ∷
   rw 13 q5 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q6 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 10 q16 ∷
   rw 9 q7 ∷
   rw⁻ 8 q4 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q1 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "乔") ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q2 ∷
   rw 9 q5 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q11 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q12 ∷
   rw 10 q18 ∷
   rw 9 q14 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q15 ∷
   re 9 5 (ℓ "乑") ∷
   rw 11 q7 ∷
   rw⁻ 10 q4 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q3 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q2 ∷
   rw 11 q5 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q6 ∷
   rw 6 q19 ∷
   rw 0 q20 ∷
   rw 36 q11 ∷
   rw 35 q21 ∷
   rw 34 q21 ∷
   rw 33 q22 ∷
   rw 32 q21 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q15 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q15 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q15 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q15 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q15 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q15 ∷
   rw 27 q23 ∷
   rw⁻ 26 q21 ∷
   rw⁻ 27 q22 ∷
   rw⁻ 28 q21 ∷
   rw⁻ 29 q21 ∷
   rw 32 q11 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q11 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q11 ∷
   re 32 3 (ℓ "乑") ∷
   rw 35 q11 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q11 ∷
   re 34 3 (ℓ "乑") ∷
   rw 37 q11 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q15 ∷
   rw⁻ 25 q24 ∷
   rw⁻ 26 q25 ∷
   rw⁻ 27 q24 ∷
   rw⁻ 28 q24 ∷
   rw 29 q11 ∷
   rw 28 q21 ∷
   rw 27 q21 ∷
   rw 26 q22 ∷
   rw 25 q21 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q15 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q15 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q15 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q15 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q15 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q15 ∷
   rw 18 q26 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q15 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q15 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q15 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q15 ∷
   rw 13 q26 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q15 ∷
   rw 11 q26 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q15 ∷
   rw 11 q27 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q22 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q21 ∷
   rw 16 q11 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q28 ∷
   rw 18 q11 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q28 ∷
   rw 20 q11 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q11 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q11 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q11 ∷
   re 21 3 (ℓ "乑") ∷
   rw 22 q28 ∷
   rw 25 q11 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q11 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q11 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q11 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q11 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q11 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q15 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q25 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q24 ∷
   rw 3 q23 ∷
   rw 37 q7 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q2 ∷
   rw 36 q1 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (ℓ "乔") ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q2 ∷
   rw 37 q5 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q6 ∷
   re 36 1 (ℓ "乏丼临丼乏") ∷
   rw 42 q11 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q29 ∷
   rw 38 q30 ∷
   rw 37 q31 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q15 ∷
   re 37 5 (ℓ "乑") ∷
   rw 39 q7 ∷
   rw⁻ 38 q4 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw⁻ 39 q2 ∷
   rw 38 q1 ∷
   rw⁻ 37 q2 ∷
   re 38 3 (ℓ "乔") ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q2 ∷
   rw 39 q5 ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q6 ∷
   rw 36 q7 ∷
   rw⁻ 35 q4 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q2 ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (ℓ "乔") ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q2 ∷
   rw 36 q5 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q6 ∷
   re 35 1 (ℓ "乏丼临丼乏") ∷
   rw 41 q11 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q29 ∷
   rw 37 q30 ∷
   rw 36 q31 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q15 ∷
   re 36 5 (ℓ "乑") ∷
   rw 38 q7 ∷
   rw⁻ 37 q4 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw⁻ 38 q2 ∷
   rw 37 q1 ∷
   rw⁻ 36 q2 ∷
   re 37 3 (ℓ "乔") ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 38 1 (ℓ "乏乇乏") ∷
   rw 37 q2 ∷
   rw 38 q5 ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "乑") ∷
   rw 38 q6 ∷
   rw 35 q7 ∷
   rw⁻ 34 q4 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q2 ∷
   rw 34 q8 ∷
   rw⁻ 33 q2 ∷
   re 34 3 (ℓ "丽") ∷
   rw 34 q9 ∷
   rw 33 q4 ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q2 ∷
   rw 35 q10 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q6 ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q11 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q29 ∷
   rw 36 q32 ∷
   rw 35 q31 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q15 ∷
   re 35 5 (ℓ "中") ∷
   rw 37 q7 ∷
   rw⁻ 36 q4 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q2 ∷
   rw 36 q8 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (ℓ "丽") ∷
   rw 36 q9 ∷
   rw 35 q4 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q2 ∷
   rw 37 q10 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q6 ∷
   rw 34 q7 ∷
   rw⁻ 33 q4 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q2 ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 33 3 (ℓ "乔") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q2 ∷
   rw 34 q5 ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乑") ∷
   rw 34 q6 ∷
   re 33 1 (ℓ "乏丼临丼乏") ∷
   rw 39 q11 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q29 ∷
   rw 35 q30 ∷
   rw 34 q31 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q15 ∷
   re 34 5 (ℓ "乑") ∷
   rw 36 q7 ∷
   rw⁻ 35 q4 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q2 ∷
   rw 35 q1 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (ℓ "乔") ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q2 ∷
   rw 36 q5 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q6 ∷
   rw 33 q7 ∷
   rw⁻ 32 q4 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q2 ∷
   rw 32 q8 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q9 ∷
   rw 31 q4 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q2 ∷
   rw 33 q10 ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q6 ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q11 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q29 ∷
   rw 34 q32 ∷
   rw 33 q31 ∷ []) Eq.refl
