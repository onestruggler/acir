{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D226 (W : Ws) where

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
  q9 = wE 113 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = wE 114 W
  q12 : Eqn
  q12 = wE 3 W
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

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part8: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part8 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中中丘乆並乏丶乏丘並中中中中中中乌中中中乑中中両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘丧丧丧乄丧丧乌両両両両両両丏丵両両両中中中中中中乑业中乏丧乏乏丧丧丧丧丧丧丧乏乌中中中乑中中丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part8 = derive (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丧丧丧乄丧丧乌中中中中中中乑业中中丘乆並乏丶乏丘並中中中中中中乌中中中乑中中両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘丧丧丧乄丧丧乌両両両両両両丏丵両両両中中中中中中乑业中乏丧乏乏丧丧丧丧丧丧丧乏乌中中中乑中中丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (re 59 3 (ℓ "丽") ∷
   rw 59 q1 ∷
   rw 58 q2 ∷
   re 60 1 (ℓ "乏丶乏") ∷
   rw 59 q3 ∷
   rw 60 q4 ∷
   rw 61 q3 ∷
   re 59 3 (ℓ "中") ∷
   rw 60 q5 ∷
   rw 57 q6 ∷
   rw⁻ 56 q2 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q3 ∷
   rw 56 q7 ∷
   rw⁻ 55 q3 ∷
   re 56 3 (ℓ "丽") ∷
   rw 56 q1 ∷
   rw 55 q2 ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q3 ∷
   rw 57 q4 ∷
   rw 58 q3 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q5 ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q8 ∷
   re 60 3 (ℓ "乓") ∷
   rw 59 q9 ∷
   rw 58 q10 ∷
   rw 57 q11 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q12 ∷
   re 57 5 (ℓ "中") ∷
   rw 59 q6 ∷
   rw⁻ 58 q2 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q3 ∷
   rw 58 q7 ∷
   rw⁻ 57 q3 ∷
   re 58 3 (ℓ "丽") ∷
   rw 58 q1 ∷
   rw 57 q2 ∷
   re 59 1 (ℓ "乏丶乏") ∷
   rw 58 q3 ∷
   rw 59 q4 ∷
   rw 60 q3 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q5 ∷
   rw 56 q6 ∷
   rw⁻ 55 q2 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q3 ∷
   rw 55 q7 ∷
   rw⁻ 54 q3 ∷
   re 55 3 (ℓ "丽") ∷
   rw 55 q1 ∷
   rw 54 q2 ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q3 ∷
   rw 56 q4 ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "中") ∷
   rw 56 q5 ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q8 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q9 ∷
   rw 57 q10 ∷
   rw 56 q11 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q12 ∷
   re 56 5 (ℓ "中") ∷
   rw 58 q6 ∷
   rw⁻ 57 q2 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q3 ∷
   rw 57 q7 ∷
   rw⁻ 56 q3 ∷
   re 57 3 (ℓ "丽") ∷
   rw 57 q1 ∷
   rw 56 q2 ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q3 ∷
   rw 58 q4 ∷
   rw 59 q3 ∷
   re 57 3 (ℓ "中") ∷
   rw 58 q5 ∷
   rw⁻ 53 q13 ∷
   rw⁻ 54 q14 ∷
   rw⁻ 55 q13 ∷
   rw 54 q6 ∷
   rw⁻ 53 q2 ∷
   re 52 1 (ℓ "乏乄乏") ∷
   rw⁻ 54 q3 ∷
   rw 53 q15 ∷
   rw⁻ 52 q3 ∷
   re 53 3 (ℓ "乔") ∷
   rw 53 q16 ∷
   rw 52 q2 ∷
   re 54 1 (ℓ "乏乇乏") ∷
   rw 53 q3 ∷
   rw 54 q17 ∷
   rw 55 q3 ∷
   re 53 3 (ℓ "乑") ∷
   rw 54 q5 ∷
   re 53 1 (ℓ "乏丼临丼乏") ∷
   rw 59 q8 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q9 ∷
   rw 55 q18 ∷
   rw 54 q11 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q12 ∷
   re 54 5 (ℓ "乑") ∷
   rw 56 q6 ∷
   rw⁻ 55 q2 ∷
   re 54 1 (ℓ "乏乄乏") ∷
   rw⁻ 56 q3 ∷
   rw 55 q15 ∷
   rw⁻ 54 q3 ∷
   re 55 3 (ℓ "乔") ∷
   rw 55 q16 ∷
   rw 54 q2 ∷
   re 56 1 (ℓ "乏乇乏") ∷
   rw 55 q3 ∷
   rw 56 q17 ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "乑") ∷
   rw 56 q5 ∷
   rw 53 q6 ∷
   rw⁻ 52 q2 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q3 ∷
   rw 52 q7 ∷
   rw⁻ 51 q3 ∷
   re 52 3 (ℓ "丽") ∷
   rw 52 q1 ∷
   rw 51 q2 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q5 ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q8 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q9 ∷
   rw 54 q10 ∷
   rw 53 q11 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q12 ∷
   re 53 5 (ℓ "中") ∷
   rw 55 q6 ∷
   rw⁻ 54 q2 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q3 ∷
   rw 54 q7 ∷
   rw⁻ 53 q3 ∷
   re 54 3 (ℓ "丽") ∷
   rw 54 q1 ∷
   rw 53 q2 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q3 ∷
   rw 55 q4 ∷
   rw 56 q3 ∷
   re 54 3 (ℓ "中") ∷
   rw 55 q5 ∷
   rw 52 q6 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q3 ∷
   rw 51 q7 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (ℓ "丽") ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q3 ∷
   rw 52 q4 ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q5 ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q8 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q9 ∷
   rw 53 q10 ∷
   rw 52 q11 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q12 ∷
   re 52 5 (ℓ "中") ∷
   rw 54 q6 ∷
   rw⁻ 53 q2 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q3 ∷
   rw 53 q7 ∷
   rw⁻ 52 q3 ∷
   re 53 3 (ℓ "丽") ∷
   rw 53 q1 ∷
   rw 52 q2 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q3 ∷
   rw 54 q4 ∷
   rw 55 q3 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q5 ∷
   rw 51 q6 ∷
   rw⁻ 50 q2 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q3 ∷
   rw 50 q7 ∷
   rw⁻ 49 q3 ∷
   re 50 3 (ℓ "丽") ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q3 ∷
   rw 51 q4 ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q5 ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q8 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q9 ∷
   rw 52 q10 ∷
   rw 51 q11 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q12 ∷
   re 51 5 (ℓ "中") ∷
   rw 53 q6 ∷
   rw⁻ 52 q2 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q3 ∷
   rw 52 q7 ∷
   rw⁻ 51 q3 ∷
   re 52 3 (ℓ "丽") ∷
   rw 52 q1 ∷
   rw 51 q2 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q5 ∷
   rw 50 q6 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q3 ∷
   rw 49 q7 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (ℓ "丽") ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q3 ∷
   rw 50 q4 ∷
   rw 51 q3 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q5 ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q8 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q9 ∷
   rw 51 q10 ∷
   rw 50 q11 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q12 ∷
   re 50 5 (ℓ "中") ∷
   rw 52 q6 ∷
   rw⁻ 51 q2 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q3 ∷
   rw 51 q7 ∷
   rw⁻ 50 q3 ∷
   re 51 3 (ℓ "丽") ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q3 ∷
   rw 52 q4 ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q5 ∷
   rw 49 q6 ∷
   rw⁻ 48 q2 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q3 ∷
   rw 48 q7 ∷
   rw⁻ 47 q3 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q1 ∷
   rw 47 q2 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q3 ∷
   rw 49 q4 ∷
   rw 50 q3 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q5 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q8 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q9 ∷
   rw 50 q10 ∷
   rw 49 q11 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q12 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q6 ∷
   rw⁻ 50 q2 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q3 ∷
   rw 50 q7 ∷
   rw⁻ 49 q3 ∷
   re 50 3 (ℓ "丽") ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q3 ∷
   rw 51 q4 ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q5 ∷
   rw 48 q6 ∷
   rw⁻ 47 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q3 ∷
   rw 47 q7 ∷
   rw⁻ 46 q3 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q3 ∷
   rw 48 q4 ∷
   rw 49 q3 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q5 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q8 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q9 ∷
   rw 49 q10 ∷
   rw 48 q11 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q12 ∷
   re 48 5 (ℓ "中") ∷
   rw 50 q6 ∷
   rw⁻ 49 q2 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q3 ∷
   rw 49 q7 ∷
   rw⁻ 48 q3 ∷
   re 49 3 (ℓ "丽") ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q3 ∷
   rw 50 q4 ∷
   rw 51 q3 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q5 ∷
   rw 45 q19 ∷
   rw 39 q20 ∷
   rw 84 q8 ∷
   rw 83 q21 ∷
   rw 82 q21 ∷
   rw 81 q21 ∷
   rw 80 q22 ∷
   rw 79 q23 ∷
   rw 78 q21 ∷
   rw 77 q21 ∷
   rw 76 q21 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q21 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q12 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q12 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q12 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q12 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q12 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q12 ∷
   rw 68 q24 ∷
   rw⁻ 67 q21 ∷
   rw⁻ 68 q21 ∷
   rw⁻ 69 q21 ∷
   rw⁻ 70 q21 ∷
   rw⁻ 71 q21 ∷
   rw⁻ 72 q21 ∷
   rw⁻ 73 q23 ∷
   rw⁻ 74 q22 ∷
   rw⁻ 75 q21 ∷
   rw⁻ 76 q21 ∷
   rw⁻ 77 q21 ∷
   rw 80 q8 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q8 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q8 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q8 ∷
   re 81 3 (ℓ "乑") ∷
   rw 84 q8 ∷
   re 82 3 (ℓ "中") ∷
   rw 85 q8 ∷
   re 83 3 (ℓ "中") ∷
   rw 84 q12 ∷
   rw⁻ 66 q25 ∷
   rw⁻ 67 q25 ∷
   rw⁻ 68 q25 ∷
   rw⁻ 69 q25 ∷
   rw⁻ 70 q25 ∷
   rw⁻ 71 q25 ∷
   rw⁻ 72 q26 ∷
   rw⁻ 73 q27 ∷
   rw⁻ 74 q25 ∷
   rw⁻ 75 q25 ∷
   rw⁻ 76 q25 ∷
   rw 77 q8 ∷
   rw 76 q21 ∷
   rw 75 q21 ∷
   rw 74 q21 ∷
   rw 73 q22 ∷
   rw 72 q23 ∷
   rw 71 q21 ∷
   rw 70 q21 ∷
   rw 69 q21 ∷
   rw 68 q21 ∷
   rw 67 q21 ∷
   rw 66 q21 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q12 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q12 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q12 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q12 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q12 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q12 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q12 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q12 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q12 ∷
   rw 56 q28 ∷
   re 55 1 (ℓ "乏乄乏") ∷
   rw 57 q12 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q12 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q12 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q12 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q12 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q12 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q12 ∷
   rw 50 q29 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q21 ∷
   rw⁻ 51 q21 ∷
   rw⁻ 52 q21 ∷
   rw⁻ 53 q21 ∷
   rw⁻ 54 q21 ∷
   rw⁻ 55 q23 ∷
   rw⁻ 56 q22 ∷
   rw⁻ 57 q21 ∷
   rw⁻ 58 q21 ∷
   rw⁻ 59 q21 ∷
   rw 62 q8 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q8 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q8 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q8 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q8 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q8 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q8 ∷
   re 66 3 (ℓ "乑") ∷
   rw 67 q30 ∷
   rw 70 q8 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q8 ∷ []) Eq.refl
