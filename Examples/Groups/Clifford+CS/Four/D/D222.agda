{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D222 (W : Ws) where

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
  q1 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q2 : Eqn
  q2 = eqn (ℓ "丏乌") (ℓ "乌丏") (low-comm (((S • S • S) ↑)) (CX₀₁))
  q3 : Eqn
  q3 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q4 : Eqn
  q4 = wE 558 W
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 629 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 113 W
  q14 : Eqn
  q14 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = wE 114 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = wE 630 W
  q19 : Eqn
  q19 = wE 142 W
  q20 : Eqn
  q20 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q21 : Eqn
  q21 = wE 673 W

-- Bar(SSSKSS;2,3->0) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (ℓ "丘丷丘両丵両両丘乆丘丧丧丧乄丧丧乌両両両両両両丏丵両両両中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧丧乄丧丧乌中中中中中中乑业中中丘乏丼丠乖丼乏丘中中中中中中乌中中中乑中中丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (ℓ "丘丷丘両丵両両丘乆丘丧丧丧乄丧丧乌両両両両両両丏丵両両両中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘") (ℓ "丘丷丘両丵両両丘乆丘両両両両両両丏丵両両両丧丧丧乄丧丧乌中中中中中中乑业中中丘乏丼丠乖丼乏丘中中中中中中乌中中中乑中中丘丨久丨丨丘丘丧丧丧丘両丵両両丘乆丘両両両両両両丏丵両両両丘乆丘丘丨久丨丨丘丘丨丨丨丘")
  (rw⁻ 16 q1 ∷
   rw⁻ 17 q1 ∷
   rw⁻ 18 q1 ∷
   rw⁻ 19 q1 ∷
   rw⁻ 20 q1 ∷
   rw⁻ 21 q1 ∷
   rw⁻ 22 q2 ∷
   rw⁻ 23 q3 ∷
   rw⁻ 24 q1 ∷
   rw⁻ 25 q1 ∷
   rw⁻ 26 q1 ∷
   rw 10 q4 ∷
   rw 53 q5 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw⁻ 53 q7 ∷
   rw 52 q8 ∷
   rw⁻ 51 q7 ∷
   re 52 3 (ℓ "丽") ∷
   rw 52 q9 ∷
   rw 51 q6 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q7 ∷
   rw 53 q10 ∷
   rw 54 q7 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q11 ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q12 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q13 ∷
   rw 54 q14 ∷
   rw 53 q15 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q16 ∷
   re 53 5 (ℓ "中") ∷
   rw 55 q5 ∷
   rw⁻ 54 q6 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q7 ∷
   rw 54 q8 ∷
   rw⁻ 53 q7 ∷
   re 54 3 (ℓ "丽") ∷
   rw 54 q9 ∷
   rw 53 q6 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q7 ∷
   rw 55 q10 ∷
   rw 56 q7 ∷
   re 54 3 (ℓ "中") ∷
   rw 55 q11 ∷
   rw 52 q5 ∷
   rw⁻ 51 q6 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q7 ∷
   rw 51 q8 ∷
   rw⁻ 50 q7 ∷
   re 51 3 (ℓ "丽") ∷
   rw 51 q9 ∷
   rw 50 q6 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q7 ∷
   rw 52 q10 ∷
   rw 53 q7 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q11 ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q12 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q13 ∷
   rw 53 q14 ∷
   rw 52 q15 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q16 ∷
   re 52 5 (ℓ "中") ∷
   rw 54 q5 ∷
   rw⁻ 53 q6 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q7 ∷
   rw 53 q8 ∷
   rw⁻ 52 q7 ∷
   re 53 3 (ℓ "丽") ∷
   rw 53 q9 ∷
   rw 52 q6 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q7 ∷
   rw 54 q10 ∷
   rw 55 q7 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q11 ∷
   rw 51 q5 ∷
   rw⁻ 50 q6 ∷
   re 49 1 (ℓ "乏乄乏") ∷
   rw⁻ 51 q7 ∷
   rw 50 q17 ∷
   rw⁻ 49 q7 ∷
   re 50 3 (ℓ "乔") ∷
   rw 50 q18 ∷
   rw 49 q6 ∷
   re 51 1 (ℓ "乏乇乏") ∷
   rw 50 q7 ∷
   rw 51 q19 ∷
   rw 52 q7 ∷
   re 50 3 (ℓ "乑") ∷
   rw 51 q11 ∷
   re 50 1 (ℓ "乏丼临丼乏") ∷
   rw 56 q12 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q13 ∷
   rw 52 q20 ∷
   rw 51 q15 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q16 ∷
   re 51 5 (ℓ "乑") ∷
   rw 53 q5 ∷
   rw⁻ 52 q6 ∷
   re 51 1 (ℓ "乏乄乏") ∷
   rw⁻ 53 q7 ∷
   rw 52 q17 ∷
   rw⁻ 51 q7 ∷
   re 52 3 (ℓ "乔") ∷
   rw 52 q18 ∷
   rw 51 q6 ∷
   re 53 1 (ℓ "乏乇乏") ∷
   rw 52 q7 ∷
   rw 53 q19 ∷
   rw 54 q7 ∷
   re 52 3 (ℓ "乑") ∷
   rw 53 q11 ∷
   rw 50 q5 ∷
   rw⁻ 49 q6 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q7 ∷
   rw 49 q8 ∷
   rw⁻ 48 q7 ∷
   re 49 3 (ℓ "丽") ∷
   rw 49 q9 ∷
   rw 48 q6 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q7 ∷
   rw 50 q10 ∷
   rw 51 q7 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q11 ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q12 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q13 ∷
   rw 51 q14 ∷
   rw 50 q15 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q16 ∷
   re 50 5 (ℓ "中") ∷
   rw 52 q5 ∷
   rw⁻ 51 q6 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw⁻ 52 q7 ∷
   rw 51 q8 ∷
   rw⁻ 50 q7 ∷
   re 51 3 (ℓ "丽") ∷
   rw 51 q9 ∷
   rw 50 q6 ∷
   re 52 1 (ℓ "乏丶乏") ∷
   rw 51 q7 ∷
   rw 52 q10 ∷
   rw 53 q7 ∷
   re 51 3 (ℓ "中") ∷
   rw 52 q11 ∷
   rw 49 q5 ∷
   rw⁻ 48 q6 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw⁻ 49 q7 ∷
   rw 48 q8 ∷
   rw⁻ 47 q7 ∷
   re 48 3 (ℓ "丽") ∷
   rw 48 q9 ∷
   rw 47 q6 ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q7 ∷
   rw 49 q10 ∷
   rw 50 q7 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q11 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q12 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q13 ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q16 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q5 ∷
   rw⁻ 50 q6 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q7 ∷
   rw 50 q8 ∷
   rw⁻ 49 q7 ∷
   re 50 3 (ℓ "丽") ∷
   rw 50 q9 ∷
   rw 49 q6 ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q7 ∷
   rw 51 q10 ∷
   rw 52 q7 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q11 ∷
   rw 48 q5 ∷
   rw⁻ 47 q6 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q7 ∷
   rw 47 q8 ∷
   rw⁻ 46 q7 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q7 ∷
   rw 48 q10 ∷
   rw 49 q7 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q11 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q12 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q13 ∷
   rw 49 q14 ∷
   rw 48 q15 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q16 ∷
   re 48 5 (ℓ "中") ∷
   rw 50 q5 ∷
   rw⁻ 49 q6 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw⁻ 50 q7 ∷
   rw 49 q8 ∷
   rw⁻ 48 q7 ∷
   re 49 3 (ℓ "丽") ∷
   rw 49 q9 ∷
   rw 48 q6 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q7 ∷
   rw 50 q10 ∷
   rw 51 q7 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q11 ∷
   rw 45 q21 ∷
   rw 46 q5 ∷
   rw⁻ 45 q6 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q7 ∷
   rw 45 q8 ∷
   rw⁻ 44 q7 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q9 ∷
   rw 44 q6 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q7 ∷
   rw 46 q10 ∷
   rw 47 q7 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q11 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q12 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q13 ∷
   rw 47 q14 ∷
   rw 46 q15 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q16 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q5 ∷
   rw⁻ 47 q6 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q7 ∷
   rw 47 q8 ∷
   rw⁻ 46 q7 ∷
   re 47 3 (ℓ "丽") ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q7 ∷
   rw 48 q10 ∷
   rw 49 q7 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q11 ∷
   rw 45 q5 ∷
   rw⁻ 44 q6 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q7 ∷
   rw 44 q8 ∷
   rw⁻ 43 q7 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q9 ∷
   rw 43 q6 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q7 ∷
   rw 45 q10 ∷
   rw 46 q7 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q11 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q12 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q13 ∷
   rw 46 q14 ∷
   rw 45 q15 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q16 ∷
   re 45 5 (ℓ "中") ∷
   rw 47 q5 ∷
   rw⁻ 46 q6 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw⁻ 47 q7 ∷
   rw 46 q8 ∷
   rw⁻ 45 q7 ∷
   re 46 3 (ℓ "丽") ∷
   rw 46 q9 ∷
   rw 45 q6 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q7 ∷
   rw 47 q10 ∷
   rw 48 q7 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q11 ∷
   rw 44 q5 ∷
   rw⁻ 43 q6 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q7 ∷
   rw 43 q8 ∷
   rw⁻ 42 q7 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q9 ∷
   rw 42 q6 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q7 ∷
   rw 44 q10 ∷
   rw 45 q7 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q11 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q12 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q13 ∷
   rw 45 q14 ∷
   rw 44 q15 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q16 ∷
   re 44 5 (ℓ "中") ∷
   rw 46 q5 ∷
   rw⁻ 45 q6 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw⁻ 46 q7 ∷
   rw 45 q8 ∷
   rw⁻ 44 q7 ∷
   re 45 3 (ℓ "丽") ∷
   rw 45 q9 ∷
   rw 44 q6 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q7 ∷
   rw 46 q10 ∷
   rw 47 q7 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q11 ∷
   rw 43 q5 ∷
   rw⁻ 42 q6 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q7 ∷
   rw 42 q8 ∷
   rw⁻ 41 q7 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q9 ∷
   rw 41 q6 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q7 ∷
   rw 43 q10 ∷
   rw 44 q7 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q11 ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q12 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q13 ∷
   rw 44 q14 ∷
   rw 43 q15 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q16 ∷
   re 43 5 (ℓ "中") ∷
   rw 45 q5 ∷
   rw⁻ 44 q6 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw⁻ 45 q7 ∷
   rw 44 q8 ∷
   rw⁻ 43 q7 ∷
   re 44 3 (ℓ "丽") ∷
   rw 44 q9 ∷
   rw 43 q6 ∷
   re 45 1 (ℓ "乏丶乏") ∷
   rw 44 q7 ∷
   rw 45 q10 ∷
   rw 46 q7 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q11 ∷
   rw 42 q5 ∷
   rw⁻ 41 q6 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw⁻ 42 q7 ∷
   rw 41 q8 ∷
   rw⁻ 40 q7 ∷
   re 41 3 (ℓ "丽") ∷
   rw 41 q9 ∷
   rw 40 q6 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q7 ∷
   rw 42 q10 ∷
   rw 43 q7 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q11 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q12 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q13 ∷
   rw 43 q14 ∷
   rw 42 q15 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q16 ∷
   re 42 5 (ℓ "中") ∷
   rw 44 q5 ∷
   rw⁻ 43 q6 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw⁻ 44 q7 ∷
   rw 43 q8 ∷
   rw⁻ 42 q7 ∷
   re 43 3 (ℓ "丽") ∷
   rw 43 q9 ∷
   rw 42 q6 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q7 ∷
   rw 44 q10 ∷
   rw 45 q7 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q11 ∷
   rw 41 q5 ∷
   rw⁻ 40 q6 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw⁻ 41 q7 ∷
   rw 40 q8 ∷
   rw⁻ 39 q7 ∷
   re 40 3 (ℓ "丽") ∷
   rw 40 q9 ∷
   rw 39 q6 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q7 ∷
   rw 41 q10 ∷
   rw 42 q7 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q11 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q12 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q13 ∷
   rw 42 q14 ∷
   rw 41 q15 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q16 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q5 ∷
   rw⁻ 42 q6 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw⁻ 43 q7 ∷
   rw 42 q8 ∷
   rw⁻ 41 q7 ∷
   re 42 3 (ℓ "丽") ∷
   rw 42 q9 ∷
   rw 41 q6 ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q7 ∷
   rw 43 q10 ∷
   rw 44 q7 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q11 ∷
   rw 40 q5 ∷
   rw⁻ 39 q6 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw⁻ 40 q7 ∷
   rw 39 q8 ∷
   rw⁻ 38 q7 ∷
   re 39 3 (ℓ "丽") ∷
   rw 39 q9 ∷
   rw 38 q6 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q7 ∷
   rw 40 q10 ∷
   rw 41 q7 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q11 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q12 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q13 ∷ []) Eq.refl
