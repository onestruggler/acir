{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D218 (W : Ws) where

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
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 629 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 31 W
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
  q13 = wE 140 W
  q14 : Eqn
  q14 = wE 630 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q17 : Eqn
  q17 = wE 739 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part0: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part0 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中丘丷並丽丘並中中中中中中乌中中中乑中中両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part0 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中丘丷並丽丘並中中中中中中乌中中中乑中中両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "丽") ∷
   rw 31 q5 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   rw 32 q6 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q7 ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q8 ∷
   re 35 3 (ℓ "举") ∷
   rw 34 q9 ∷
   rw 33 q10 ∷
   rw 32 q11 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q12 ∷
   re 32 5 (ℓ "中") ∷
   rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   rw 33 q5 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q3 ∷
   rw 34 q6 ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q7 ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q6 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q7 ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q8 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q9 ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q12 ∷
   re 31 5 (ℓ "中") ∷
   rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q3 ∷
   rw 32 q4 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (ℓ "丽") ∷
   rw 32 q5 ∷
   rw 31 q2 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q3 ∷
   rw 33 q6 ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q7 ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q13 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "乔") ∷
   rw 29 q14 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q3 ∷
   rw 30 q15 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "乑") ∷
   rw 30 q7 ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q8 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q9 ∷
   rw 31 q16 ∷
   rw 30 q11 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q12 ∷
   re 30 5 (ℓ "乑") ∷
   rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q3 ∷
   rw 31 q13 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q14 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q3 ∷
   rw 32 q15 ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q7 ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q7 ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q8 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q9 ∷
   rw 30 q10 ∷
   rw 29 q11 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q12 ∷
   re 29 5 (ℓ "中") ∷
   rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q5 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q3 ∷
   rw 31 q6 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q7 ∷
   rw 28 q1 ∷
   rw⁻ 27 q2 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q3 ∷
   rw 27 q4 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q5 ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q3 ∷
   rw 28 q6 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q7 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q8 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 28 q11 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q12 ∷
   re 28 5 (ℓ "中") ∷
   rw 30 q1 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (ℓ "丽") ∷
   rw 29 q5 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q3 ∷
   rw 30 q6 ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q7 ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q5 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q7 ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q8 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q9 ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q12 ∷
   re 27 5 (ℓ "中") ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (ℓ "丽") ∷
   rw 28 q5 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q3 ∷
   rw 29 q6 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   rw 29 q7 ∷
   rw 24 q17 ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q4 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q5 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q6 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q8 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q12 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q1 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q5 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   rw 27 q6 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q7 ∷
   rw 24 q1 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q4 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q5 ∷
   rw 22 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   rw 24 q6 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q7 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q8 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q11 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q12 ∷
   re 24 5 (ℓ "中") ∷
   rw 26 q1 ∷
   rw⁻ 25 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q4 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q5 ∷
   rw 24 q2 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   rw 26 q6 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q7 ∷
   rw 23 q1 ∷
   rw⁻ 22 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q5 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q6 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q7 ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q8 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q9 ∷
   rw 24 q10 ∷
   rw 23 q11 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q12 ∷
   re 23 5 (ℓ "中") ∷
   rw 25 q1 ∷
   rw⁻ 24 q2 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q3 ∷
   rw 24 q4 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (ℓ "丽") ∷
   rw 24 q5 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q6 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q7 ∷
   rw 22 q1 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q4 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q5 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q6 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q7 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q8 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q9 ∷
   rw 23 q10 ∷
   rw 22 q11 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q12 ∷
   re 22 5 (ℓ "中") ∷
   rw 24 q1 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q4 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q5 ∷
   rw 22 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   rw 24 q6 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q7 ∷
   rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q4 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q5 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q6 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q7 ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q8 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q9 ∷
   rw 22 q10 ∷
   rw 21 q11 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q12 ∷
   re 21 5 (ℓ "中") ∷
   rw 23 q1 ∷
   rw⁻ 22 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q5 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q6 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q7 ∷
   rw 20 q1 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q4 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (ℓ "丽") ∷
   rw 19 q5 ∷
   rw 18 q2 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q3 ∷
   rw 20 q6 ∷
   rw 21 q3 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q7 ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q8 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   rw 20 q11 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q12 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q1 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q4 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q5 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q6 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q7 ∷
   rw 19 q1 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q4 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q5 ∷
   rw 17 q2 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q3 ∷
   rw 19 q6 ∷
   rw 20 q3 ∷
   re 18 3 (ℓ "中") ∷
   rw 19 q7 ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q8 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   rw 19 q11 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q12 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q1 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q4 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷ []) Eq.refl
