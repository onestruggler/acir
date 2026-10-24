{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D219 (W : Ws) where

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
  q6 = wE 5 W
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 21 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q11 : Eqn
  q11 = wE 51 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 739 W
  q20 : Eqn
  q20 = wE 554 W
  q21 : Eqn
  q21 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = wE 555 W
  q24 : Eqn
  q24 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q25 : Eqn
  q25 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q26 : Eqn
  q26 = wE 464 W
  q27 : Eqn
  q27 = wE 556 W
  q28 : Eqn
  q28 = wE 151 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中丘丷並丽丘並中中中中中中乌中中中乑中中両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中丘中乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中丘丷並丽丘並中中中中中中乌中中中乑中中両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中丘中乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 20 q1 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q5 ∷
   rw 18 q6 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q7 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (ℓ "丽") ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q5 ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q8 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q11 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q12 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q6 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q7 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q1 ∷
   rw 18 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q5 ∷
   rw 17 q6 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q7 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "丽") ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "中") ∷
   rw 17 q5 ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q8 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   rw 17 q11 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q12 ∷
   re 17 5 (ℓ "中") ∷
   rw 19 q6 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q7 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q5 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 16 q13 ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q15 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "乔") ∷
   rw 14 q16 ∷
   rw 13 q2 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q3 ∷
   rw 15 q17 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q5 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q8 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q9 ∷
   rw 16 q18 ∷
   rw 15 q11 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q12 ∷
   re 15 5 (ℓ "乑") ∷
   rw 17 q6 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q15 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (ℓ "乔") ∷
   rw 16 q16 ∷
   rw 15 q2 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q3 ∷
   rw 17 q17 ∷
   rw 18 q3 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q5 ∷
   rw 14 q6 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q7 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q1 ∷
   rw 12 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q5 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q8 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q12 ∷
   re 14 5 (ℓ "中") ∷
   rw 16 q6 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q7 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (ℓ "丽") ∷
   rw 15 q1 ∷
   rw 14 q2 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q3 ∷
   rw 16 q4 ∷
   rw 17 q3 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q5 ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q7 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q5 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q8 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q12 ∷
   re 13 5 (ℓ "中") ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q3 ∷
   rw 14 q7 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (ℓ "丽") ∷
   rw 14 q1 ∷
   rw 13 q2 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q3 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q5 ∷
   rw 12 q6 ∷
   rw⁻ 11 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q3 ∷
   rw 11 q7 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q1 ∷
   rw 10 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q5 ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q8 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q12 ∷
   re 12 5 (ℓ "中") ∷
   rw 14 q6 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q3 ∷
   rw 13 q7 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (ℓ "丽") ∷
   rw 13 q1 ∷
   rw 12 q2 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q5 ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q7 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q1 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q3 ∷
   rw 11 q4 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q5 ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q8 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   rw 11 q11 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q12 ∷
   re 11 5 (ℓ "中") ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q3 ∷
   rw 12 q7 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q5 ∷
   rw 10 q6 ∷
   rw⁻ 9 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q3 ∷
   rw 9 q7 ∷
   rw⁻ 8 q3 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q1 ∷
   rw 8 q2 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q3 ∷
   rw 10 q4 ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q8 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q12 ∷
   re 10 5 (ℓ "中") ∷
   rw 12 q6 ∷
   rw⁻ 11 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q3 ∷
   rw 11 q7 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (ℓ "丽") ∷
   rw 11 q1 ∷
   rw 10 q2 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q5 ∷
   rw 9 q6 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q3 ∷
   rw 8 q7 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (ℓ "丽") ∷
   rw 8 q1 ∷
   rw 7 q2 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q4 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q5 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q12 ∷
   re 9 5 (ℓ "中") ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q3 ∷
   rw 10 q7 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (ℓ "丽") ∷
   rw 10 q1 ∷
   rw 9 q2 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q3 ∷
   rw 11 q4 ∷
   rw 12 q3 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q5 ∷
   rw 6 q19 ∷
   rw 0 q20 ∷
   rw 38 q8 ∷
   rw 37 q21 ∷
   rw 36 q21 ∷
   rw 35 q22 ∷
   rw 34 q21 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q12 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q12 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q12 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q12 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q12 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q12 ∷
   rw 29 q23 ∷
   rw⁻ 28 q21 ∷
   rw⁻ 29 q22 ∷
   rw⁻ 30 q21 ∷
   rw⁻ 31 q21 ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q8 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "乑") ∷
   rw 38 q8 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q8 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q12 ∷
   rw⁻ 27 q24 ∷
   rw⁻ 28 q25 ∷
   rw⁻ 29 q24 ∷
   rw⁻ 30 q24 ∷
   rw 31 q8 ∷
   rw 30 q21 ∷
   rw 29 q21 ∷
   rw 28 q22 ∷
   rw 27 q21 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q12 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q12 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q12 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q12 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q12 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q12 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q12 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q12 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q12 ∷
   rw 17 q26 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw 18 q12 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q12 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q12 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q12 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q12 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q12 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q12 ∷
   rw 11 q27 ∷
   rw⁻ 10 q21 ∷
   rw⁻ 11 q22 ∷
   rw⁻ 12 q21 ∷
   rw⁻ 13 q21 ∷
   rw 16 q8 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q8 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q8 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q8 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q8 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q8 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q8 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q28 ∷
   rw 24 q8 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q8 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q8 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q8 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q8 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q8 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q8 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q8 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q12 ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q25 ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q24 ∷
   rw 3 q23 ∷
   rw 39 q6 ∷
   rw⁻ 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q3 ∷
   rw 38 q7 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (ℓ "丽") ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q5 ∷ []) Eq.refl
