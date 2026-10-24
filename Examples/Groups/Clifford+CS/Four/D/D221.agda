{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D221 (W : Ws) where

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
  q20 = wE 557 W
  q21 : Eqn
  q21 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q24 : Eqn
  q24 = wE 558 W
  q25 : Eqn
  q25 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q26 : Eqn
  q26 = eqn (ℓ "丏乌") (ℓ "乌丏") (low-comm (((S • S • S) ↑)) (CX₀₁))
  q27 : Eqn
  q27 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q28 : Eqn
  q28 = wE 464 W
  q29 : Eqn
  q29 = wE 559 W
  q30 : Eqn
  q30 = wE 151 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (ℓ "丘丷丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中並丽丘並乆丘中中中中中中中乌中中中乑中中両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘丧丧丧乄丧丧乌両両両両両両丏丵両両両中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (ℓ "丘丷丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中並丽丘並乆丘中中中中中中中乌中中中乑中中両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘丧丧丧乄丧丧乌両両両両両両丏丵両両両中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 24 q1 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q3 ∷
   re 24 3 (ℓ "中") ∷
   rw 25 q5 ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "乓") ∷
   rw 27 q7 ∷
   rw 26 q8 ∷
   rw 25 q9 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q10 ∷
   re 25 5 (ℓ "中") ∷
   rw 27 q11 ∷
   rw⁻ 26 q2 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q3 ∷
   rw 26 q12 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (ℓ "丽") ∷
   rw 26 q1 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q3 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q5 ∷
   rw 24 q11 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q12 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "中") ∷
   rw 24 q5 ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "乓") ∷
   rw 26 q7 ∷
   rw 25 q8 ∷
   rw 24 q9 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q10 ∷
   re 24 5 (ℓ "中") ∷
   rw 26 q11 ∷
   rw⁻ 25 q2 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q3 ∷
   rw 25 q12 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   rw 24 q2 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q3 ∷
   rw 26 q4 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "中") ∷
   rw 26 q5 ∷
   rw⁻ 21 q13 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 23 q13 ∷
   rw 22 q11 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏乄乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q15 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "乔") ∷
   rw 21 q16 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q3 ∷
   rw 22 q17 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "乑") ∷
   rw 22 q5 ∷
   re 21 1 (ℓ "乏丼临丼乏") ∷
   rw 27 q6 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q7 ∷
   rw 23 q18 ∷
   rw 22 q9 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q10 ∷
   re 22 5 (ℓ "乑") ∷
   rw 24 q11 ∷
   rw⁻ 23 q2 ∷
   re 22 1 (ℓ "乏乄乏") ∷
   rw⁻ 24 q3 ∷
   rw 23 q15 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (ℓ "乔") ∷
   rw 23 q16 ∷
   rw 22 q2 ∷
   re 24 1 (ℓ "乏乇乏") ∷
   rw 23 q3 ∷
   rw 24 q17 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "乑") ∷
   rw 24 q5 ∷
   rw 21 q11 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q12 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
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
   rw⁻ 22 q2 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q3 ∷
   rw 22 q12 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (ℓ "丽") ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q3 ∷
   rw 23 q4 ∷
   rw 24 q3 ∷
   re 22 3 (ℓ "中") ∷
   rw 23 q5 ∷
   rw 20 q11 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q12 ∷
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
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q6 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q7 ∷
   rw 21 q8 ∷
   rw 20 q9 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q10 ∷
   re 20 5 (ℓ "中") ∷
   rw 22 q11 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q3 ∷
   rw 21 q12 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   re 21 3 (ℓ "中") ∷
   rw 22 q5 ∷
   rw 19 q11 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q12 ∷
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
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q6 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q7 ∷
   rw 20 q8 ∷
   rw 19 q9 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q10 ∷
   re 19 5 (ℓ "中") ∷
   rw 21 q11 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q3 ∷
   rw 20 q12 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   rw 19 q2 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   re 20 3 (ℓ "中") ∷
   rw 21 q5 ∷
   rw 18 q11 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q12 ∷
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
   rw 23 q6 ∷
   re 21 3 (ℓ "乓") ∷
   rw 20 q7 ∷
   rw 19 q8 ∷
   rw 18 q9 ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q10 ∷
   re 18 5 (ℓ "中") ∷
   rw 20 q11 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q3 ∷
   rw 19 q12 ∷
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
   rw 17 q11 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q3 ∷
   rw 16 q12 ∷
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
   rw 22 q6 ∷
   re 20 3 (ℓ "乓") ∷
   rw 19 q7 ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q10 ∷
   re 17 5 (ℓ "中") ∷
   rw 19 q11 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q3 ∷
   rw 18 q12 ∷
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
   rw 16 q11 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q3 ∷
   rw 15 q12 ∷
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
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q6 ∷
   re 19 3 (ℓ "乓") ∷
   rw 18 q7 ∷
   rw 17 q8 ∷
   rw 16 q9 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 15 q10 ∷
   re 16 5 (ℓ "中") ∷
   rw 18 q11 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q3 ∷
   rw 17 q12 ∷
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
   rw 13 q19 ∷
   rw 7 q20 ∷
   rw 52 q6 ∷
   rw 51 q21 ∷
   rw 50 q21 ∷
   rw 49 q21 ∷
   rw 48 q22 ∷
   rw 47 q23 ∷
   rw 46 q21 ∷
   rw 45 q21 ∷
   rw 44 q21 ∷
   rw 43 q21 ∷
   rw 42 q21 ∷
   rw 41 q21 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q10 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q10 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q10 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q10 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q10 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q10 ∷
   rw 36 q24 ∷
   rw⁻ 35 q21 ∷
   rw⁻ 36 q21 ∷
   rw⁻ 37 q21 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 39 q21 ∷
   rw⁻ 40 q21 ∷
   rw⁻ 41 q23 ∷
   rw⁻ 42 q22 ∷
   rw⁻ 43 q21 ∷
   rw⁻ 44 q21 ∷
   rw⁻ 45 q21 ∷
   rw 48 q6 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q6 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q6 ∷
   re 48 3 (ℓ "中") ∷
   rw 51 q6 ∷
   re 49 3 (ℓ "乑") ∷
   rw 52 q6 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q6 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q10 ∷
   rw⁻ 34 q25 ∷
   rw⁻ 35 q25 ∷
   rw⁻ 36 q25 ∷
   rw⁻ 37 q25 ∷
   rw⁻ 38 q25 ∷
   rw⁻ 39 q25 ∷
   rw⁻ 40 q26 ∷
   rw⁻ 41 q27 ∷
   rw⁻ 42 q25 ∷
   rw⁻ 43 q25 ∷
   rw⁻ 44 q25 ∷
   rw 45 q6 ∷
   rw 44 q21 ∷
   rw 43 q21 ∷
   rw 42 q21 ∷
   rw 41 q22 ∷
   rw 40 q23 ∷
   rw 39 q21 ∷
   rw 38 q21 ∷
   rw 37 q21 ∷
   rw 36 q21 ∷
   rw 35 q21 ∷
   rw 34 q21 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q10 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q10 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q10 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q10 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q10 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q10 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q10 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q10 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q10 ∷
   rw 24 q28 ∷
   re 23 1 (ℓ "乏乄乏") ∷
   rw 25 q10 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q10 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q10 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q10 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q10 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q10 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q10 ∷
   rw 18 q29 ∷
   rw⁻ 17 q21 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q21 ∷
   rw⁻ 20 q21 ∷
   rw⁻ 21 q21 ∷
   rw⁻ 22 q21 ∷
   rw⁻ 23 q23 ∷
   rw⁻ 24 q22 ∷
   rw⁻ 25 q21 ∷
   rw⁻ 26 q21 ∷
   rw⁻ 27 q21 ∷
   rw 30 q6 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q6 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q6 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q6 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q6 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q6 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q6 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q30 ∷
   rw 38 q6 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q6 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q6 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q6 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q6 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q6 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q6 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q6 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q6 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q10 ∷ []) Eq.refl
