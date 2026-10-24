{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D157 (W : Ws) where

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
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 113 W
  q9 : Eqn
  q9 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q10 : Eqn
  q10 = wE 114 W
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = wE 673 W
  q14 : Eqn
  q14 = wE 488 W
  q15 : Eqn
  q15 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q17 : Eqn
  q17 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q18 : Eqn
  q18 = wE 489 W
  q19 : Eqn
  q19 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q20 : Eqn
  q20 = eqn (ℓ "丏乌") (ℓ "乌丏") (low-comm (((S • S • S) ↑)) (CX₀₁))
  q21 : Eqn
  q21 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q22 : Eqn
  q22 = wE 464 W
  q23 : Eqn
  q23 = wE 490 W
  q24 : Eqn
  q24 = wE 151 W
  q25 : Eqn
  q25 = wE 7 W
  q26 : Eqn
  q26 = wE 629 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))

-- Bar(SSKSKK;2,3->0) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乏乄並乏丘並乆丘业乑业中中中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘乆丘中並並中乌中中乑中乑乑丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (ℓ "丘丷丘両丵両両丧丧乄丧乄乄乌乏乄並乏丘並乆丘业乑业中中中乑业中中中中中中乌中中乑中乑乑両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中丘乆丘中並並中乌中中乑中乑乑丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw 15 q1 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (ℓ "乔") ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q2 ∷
   rw 16 q5 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q6 ∷
   re 15 1 (ℓ "乏丼临丼乏") ∷
   rw 21 q7 ∷
   re 19 3 (ℓ "乓") ∷
   rw 18 q8 ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   re 16 1 (ℓ "乏乆乏") ∷
   rw 15 q11 ∷
   re 16 5 (ℓ "乑") ∷
   rw 18 q12 ∷
   rw⁻ 17 q4 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw⁻ 18 q2 ∷
   rw 17 q1 ∷
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
   rw 13 q13 ∷
   rw 7 q14 ∷
   rw 50 q7 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q16 ∷
   rw 45 q17 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   re 38 1 (ℓ "乏乄乏") ∷
   rw 40 q11 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q11 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q11 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q11 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q11 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q11 ∷
   rw 34 q18 ∷
   rw⁻ 33 q15 ∷
   rw⁻ 34 q15 ∷
   rw⁻ 35 q15 ∷
   rw⁻ 36 q15 ∷
   rw⁻ 37 q15 ∷
   rw⁻ 38 q15 ∷
   rw⁻ 39 q17 ∷
   rw⁻ 40 q16 ∷
   rw⁻ 41 q15 ∷
   rw⁻ 42 q15 ∷
   rw⁻ 43 q15 ∷
   rw 46 q7 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q7 ∷
   re 45 3 (ℓ "中") ∷
   rw 48 q7 ∷
   re 46 3 (ℓ "乑") ∷
   rw 49 q7 ∷
   re 47 3 (ℓ "中") ∷
   rw 50 q7 ∷
   re 48 3 (ℓ "乑") ∷
   rw 51 q7 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q11 ∷
   rw⁻ 32 q19 ∷
   rw⁻ 33 q19 ∷
   rw⁻ 34 q19 ∷
   rw⁻ 35 q19 ∷
   rw⁻ 36 q19 ∷
   rw⁻ 37 q19 ∷
   rw⁻ 38 q20 ∷
   rw⁻ 39 q21 ∷
   rw⁻ 40 q19 ∷
   rw⁻ 41 q19 ∷
   rw⁻ 42 q19 ∷
   rw 43 q7 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q16 ∷
   rw 38 q17 ∷
   rw 37 q15 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   rw 34 q15 ∷
   rw 33 q15 ∷
   rw 32 q15 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q11 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q11 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q11 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q11 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q11 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q11 ∷
   rw 25 q22 ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw 26 q11 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q11 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q11 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q11 ∷
   rw 20 q22 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q11 ∷
   rw 18 q22 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q11 ∷
   rw 18 q23 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 19 q15 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 22 q15 ∷
   rw⁻ 23 q17 ∷
   rw⁻ 24 q16 ∷
   rw⁻ 25 q15 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 27 q15 ∷
   rw 30 q7 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q24 ∷
   rw 32 q7 ∷
   re 30 3 (ℓ "乑") ∷
   rw 31 q24 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q24 ∷
   rw 39 q7 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q7 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q7 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q7 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q7 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q7 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q11 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q19 ∷
   rw⁻ 18 q19 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q20 ∷
   rw⁻ 23 q21 ∷
   rw⁻ 24 q19 ∷
   rw⁻ 25 q19 ∷
   rw⁻ 26 q19 ∷
   rw 10 q18 ∷
   rw 51 q12 ∷
   rw⁻ 50 q4 ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw⁻ 51 q2 ∷
   rw 50 q1 ∷
   rw⁻ 49 q2 ∷
   re 50 3 (ℓ "乔") ∷
   rw 50 q3 ∷
   rw 49 q4 ∷
   re 51 1 (ℓ "乏乇乏") ∷
   rw 50 q2 ∷
   rw 51 q5 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "乑") ∷
   rw 51 q6 ∷
   re 50 1 (ℓ "乏丼临丼乏") ∷
   rw 56 q7 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q8 ∷
   rw 52 q9 ∷
   rw 51 q10 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q11 ∷
   re 51 5 (ℓ "乑") ∷
   rw 53 q12 ∷
   rw⁻ 52 q4 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw⁻ 53 q2 ∷
   rw 52 q1 ∷
   rw⁻ 51 q2 ∷
   re 52 3 (ℓ "乔") ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   re 53 1 (ℓ "乏乇乏") ∷
   rw 52 q2 ∷
   rw 53 q5 ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q6 ∷
   rw 50 q12 ∷
   rw⁻ 49 q4 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw⁻ 50 q2 ∷
   rw 49 q1 ∷
   rw⁻ 48 q2 ∷
   re 49 3 (ℓ "乔") ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q2 ∷
   rw 50 q5 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q6 ∷
   re 49 1 (ℓ "乏丼临丼乏") ∷
   rw 55 q7 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q8 ∷
   rw 51 q9 ∷
   rw 50 q10 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q11 ∷
   re 50 5 (ℓ "乑") ∷
   rw 52 q12 ∷
   rw⁻ 51 q4 ∷
   re 50 1 (ℓ "乏乄乏") ∷
   rw⁻ 52 q2 ∷
   rw 51 q1 ∷
   rw⁻ 50 q2 ∷
   re 51 3 (ℓ "乔") ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   re 52 1 (ℓ "乏乇乏") ∷
   rw 51 q2 ∷
   rw 52 q5 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "乑") ∷
   rw 52 q6 ∷
   rw 49 q12 ∷
   rw⁻ 48 q4 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q2 ∷
   rw 48 q25 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q26 ∷
   rw 47 q4 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q2 ∷
   rw 49 q27 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q6 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q7 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q8 ∷
   rw 50 q28 ∷
   rw 49 q10 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q11 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q12 ∷
   rw⁻ 50 q4 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q2 ∷
   rw 50 q25 ∷
   rw⁻ 49 q2 ∷
   re 50 3 (ℓ "丽") ∷
   rw 50 q26 ∷
   rw 49 q4 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q2 ∷
   rw 51 q27 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q6 ∷
   rw 48 q12 ∷
   rw⁻ 47 q4 ∷
   re 46 1 (ℓ "乏乄乏") ∷
   rw⁻ 48 q2 ∷
   rw 47 q1 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (ℓ "乔") ∷
   rw 47 q3 ∷
   rw 46 q4 ∷
   re 48 1 (ℓ "乏乇乏") ∷
   rw 47 q2 ∷
   rw 48 q5 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "乑") ∷
   rw 48 q6 ∷
   re 47 1 (ℓ "乏丼临丼乏") ∷
   rw 53 q7 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q8 ∷
   rw 49 q9 ∷
   rw 48 q10 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q11 ∷
   re 48 5 (ℓ "乑") ∷
   rw 50 q12 ∷
   rw⁻ 49 q4 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw⁻ 50 q2 ∷
   rw 49 q1 ∷
   rw⁻ 48 q2 ∷
   re 49 3 (ℓ "乔") ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   re 50 1 (ℓ "乏乇乏") ∷
   rw 49 q2 ∷
   rw 50 q5 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "乑") ∷
   rw 50 q6 ∷
   rw 47 q12 ∷
   rw⁻ 46 q4 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q2 ∷
   rw 46 q25 ∷
   rw⁻ 45 q2 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q26 ∷
   rw 45 q4 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q2 ∷
   rw 47 q27 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q6 ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q7 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q8 ∷
   rw 48 q28 ∷
   rw 47 q10 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q11 ∷
   re 47 5 (ℓ "中") ∷
   rw 49 q12 ∷
   rw⁻ 48 q4 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q2 ∷
   rw 48 q25 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q26 ∷
   rw 47 q4 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q2 ∷
   rw 49 q27 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q6 ∷
   rw 46 q12 ∷
   rw⁻ 45 q4 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q2 ∷
   rw 45 q25 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q26 ∷
   rw 44 q4 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q2 ∷
   rw 46 q27 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q6 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q7 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q8 ∷
   rw 47 q28 ∷
   rw 46 q10 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q11 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q12 ∷
   rw⁻ 47 q4 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q2 ∷
   rw 47 q25 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q26 ∷
   rw 46 q4 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q2 ∷
   rw 48 q27 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q6 ∷
   rw 43 q13 ∷
   rw 44 q12 ∷
   rw⁻ 43 q4 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q2 ∷
   rw 43 q25 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q26 ∷
   rw 42 q4 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q2 ∷
   rw 44 q27 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q6 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q7 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q8 ∷
   rw 45 q28 ∷
   rw 44 q10 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q11 ∷
   re 44 5 (ℓ "中") ∷
   rw 46 q12 ∷
   rw⁻ 45 q4 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q2 ∷
   rw 45 q25 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q26 ∷
   rw 44 q4 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q2 ∷
   rw 46 q27 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q6 ∷
   rw 43 q12 ∷
   rw⁻ 42 q4 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q2 ∷
   rw 42 q25 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q26 ∷
   rw 41 q4 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q2 ∷
   rw 43 q27 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q6 ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q7 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q8 ∷
   rw 44 q28 ∷
   rw 43 q10 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q11 ∷
   re 43 5 (ℓ "中") ∷
   rw 45 q12 ∷
   rw⁻ 44 q4 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q2 ∷
   rw 44 q25 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q26 ∷
   rw 43 q4 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q2 ∷
   rw 45 q27 ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "中") ∷ []) Eq.refl
